//! A relatively advanced example of a staking program. If you're new to Anchor,
//! it's suggested to start with the other examples.

#![feature(proc_macro_hygiene)]

use anchor_lang::prelude::*;
use anchor_lang::solana_program::program_option::COption;
use anchor_spl::token::{self, Mint, TokenAccount, Transfer};
use lockup::{CreateVesting, RealizeLock, Realizor, Schedule, Vesting};
use std::convert::Into;

#[program]
mod registry {
    use super::*;

    #[state]
    pub struct Registry {
        pub lockup_program: Pubkey,
    }

    impl Registry {
        pub fn new(ctx: Context<State>) -> Result<Self> {
            Ok(Registry {
                lockup_program: *ctx.accounts.lockup_program.key,
            })
        }

        pub fn set_lockup_program(&mut self, ctx: Context<State>) -> Result<()> {
            self.lockup_program = *ctx.accounts.lockup_program.key;
            Ok(())
        }
    }

    impl<'info> RealizeLock<'info, IsRealized<'info>> for Registry {
        fn is_realized(ctx: Context<IsRealized>, v: Vesting) -> ProgramResult {
            if let Some(realizor) = &v.realizor {
                if &realizor.metadata != ctx.accounts.member.to_account_info().key {
                    return Err(ErrorCode::InvalidRealizorMetadata.into());
                }
                assert!(ctx.accounts.member.beneficiary == v.beneficiary);
                let total_staked =
                    ctx.accounts.member_spt.amount + ctx.accounts.member_spt_locked.amount;
                if total_staked != 0 {
                    return Err(ErrorCode::UnrealizedReward.into());
                }
            }
            Ok(())
        }
    }

    #[access_control(Initialize::accounts(&ctx, nonce))]
    pub fn initialize(
        ctx: Context<Initialize>,
        mint: Pubkey,
        authority: Pubkey,
        nonce: u8,
        withdrawal_timelock: i64,
        stake_rate: u64,
        reward_q_len: u32,
    ) -> Result<()> {
        let registrar = &mut ctx.accounts.registrar;

        registrar.authority = authority;
        registrar.nonce = nonce;
        registrar.mint = mint;
        registrar.pool_mint = *ctx.accounts.pool_mint.to_account_info().key;
        registrar.stake_rate = stake_rate;
        registrar.reward_event_q = *ctx.accounts.reward_event_q.to_account_info().key;
        registrar.withdrawal_timelock = withdrawal_timelock;

        let reward_q = &mut ctx.accounts.reward_event_q;
        reward_q
            .events
            .resize(reward_q_len as usize, Default::default());

        Ok(())
    }

    pub fn update_registrar(
        ctx: Context<UpdateRegistrar>,
        new_authority: Option<Pubkey>,
        withdrawal_timelock: Option<i64>,
    ) -> Result<()> {
        let registrar = &mut ctx.accounts.registrar;

        if let Some(new_authority) = new_authority {
            registrar.authority = new_authority;
        }

        if let Some(withdrawal_timelock) = withdrawal_timelock {
            registrar.withdrawal_timelock = withdrawal_timelock;
        }

        Ok(())
    }

    #[access_control(CreateMember::accounts(&ctx, nonce))]
    pub fn create_member(ctx: Context<CreateMember>, nonce: u8) -> Result<()> {
        let member = &mut ctx.accounts.member;
        member.registrar = *ctx.accounts.registrar.to_account_info().key;
        member.beneficiary = *ctx.accounts.beneficiary.key;
        member.balances = (&ctx.accounts.balances).into();
        member.balances_locked = (&ctx.accounts.balances_locked).into();
        member.nonce = nonce;
        Ok(())
    }

    pub fn update_member(ctx: Context<UpdateMember>, metadata: Option<Pubkey>) -> Result<()> {
        let member = &mut ctx.accounts.member;
        if let Some(m) = metadata {
            member.metadata = m;
        }
        Ok(())
    }

    // Deposits that can only come directly from the member beneficiary.
    pub fn deposit(ctx: Context<Deposit>, amount: u64) -> Result<()> {
        token::transfer(ctx.accounts.into(), amount).map_err(Into::into)
    }

    // Deposits that can only come from the beneficiary's vesting accounts.
    pub fn deposit_locked(ctx: Context<DepositLocked>, amount: u64) -> Result<()> {
        token::transfer(ctx.accounts.into(), amount).map_err(Into::into)
    }

    #[access_control(no_available_rewards(
        &ctx.accounts.reward_event_q,
        &ctx.accounts.member,
        &ctx.accounts.balances,
        &ctx.accounts.balances_locked,
    ))]
    pub fn stake(ctx: Context<Stake>, spt_amount: u64, locked: bool) -> Result<()> {
        let balances = {
            if locked {
                &ctx.accounts.balances_locked
            } else {
                &ctx.accounts.balances
            }
        };

        // Transfer tokens into the stake vault.
        {
            let seeds = &[
                ctx.accounts.registrar.to_account_info().key.as_ref(),
                ctx.accounts.member.to_account_info().key.as_ref(),
                &[ctx.accounts.member.nonce],
            ];
            let member_signer = &[&seeds[..]];
            let cpi_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.clone(),
                token::Transfer {
                    from: balances.vault.to_account_info(),
                    to: balances.vault_stake.to_account_info(),
                    authority: ctx.accounts.member_signer.to_account_info(),
                },
                member_signer,
            );
            // Convert from stake-token units to mint-token units.
            let token_amount = spt_amount
                .checked_mul(ctx.accounts.registrar.stake_rate)
                .unwrap();
            token::transfer(cpi_ctx, token_amount)?;
        }

        // Mint pool tokens to the staker.
        {
            let seeds = &[
                ctx.accounts.registrar.to_account_info().key.as_ref(),
                &[ctx.accounts.registrar.nonce],
            ];
            let registrar_signer = &[&seeds[..]];

            let cpi_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.clone(),
                token::MintTo {
                    mint: ctx.accounts.pool_mint.to_account_info(),
                    to: balances.spt.to_account_info(),
                    authority: ctx.accounts.registrar_signer.to_account_info(),
                },
                registrar_signer,
            );
            token::mint_to(cpi_ctx, spt_amount)?;
        }

        // Update stake timestamp.
        let member = &mut ctx.accounts.member;
        member.last_stake_ts = ctx.accounts.clock.unix_timestamp;

        Ok(())
    }

    #[access_control(no_available_rewards(
        &ctx.accounts.reward_event_q,
        &ctx.accounts.member,
        &ctx.accounts.balances,
        &ctx.accounts.balances_locked,
    ))]
    pub fn start_unstake(ctx: Context<StartUnstake>, spt_amount: u64, locked: bool) -> Result<()> {
        let balances = {
            if locked {
                &ctx.accounts.balances_locked
            } else {
                &ctx.accounts.balances
            }
        };

        // Program signer.
        let seeds = &[
            ctx.accounts.registrar.to_account_info().key.as_ref(),
            ctx.accounts.member.to_account_info().key.as_ref(),
            &[ctx.accounts.member.nonce],
        ];
        let member_signer = &[&seeds[..]];

        // Burn pool tokens.
        {
            let cpi_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.clone(),
                token::Burn {
                    mint: ctx.accounts.pool_mint.to_account_info(),
                    to: balances.spt.to_account_info(),
                    authority: ctx.accounts.member_signer.to_account_info(),
                },
                member_signer,
            );
            token::burn(cpi_ctx, spt_amount)?;
        }

        // Convert from stake-token units to mint-token units.
        let token_amount = spt_amount
            .checked_mul(ctx.accounts.registrar.stake_rate)
            .unwrap();

        // Transfer tokens from the stake to pending vault.
        {
            let cpi_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.clone(),
                token::Transfer {
                    from: balances.vault_stake.to_account_info(),
                    to: balances.vault_pw.to_account_info(),
                    authority: ctx.accounts.member_signer.to_account_info(),
                },
                member_signer,
            );
            token::transfer(cpi_ctx, token_amount)?;
        }

        // Print receipt.
        let pending_withdrawal = &mut ctx.accounts.pending_withdrawal;
        pending_withdrawal.burned = false;
        pending_withdrawal.member = *ctx.accounts.member.to_account_info().key;
        pending_withdrawal.start_ts = ctx.accounts.clock.unix_timestamp;
        pending_withdrawal.end_ts =
            ctx.accounts.clock.unix_timestamp + ctx.accounts.registrar.withdrawal_timelock;
        pending_withdrawal.amount = token_amount;
        pending_withdrawal.pool = ctx.accounts.registrar.pool_mint;
        pending_withdrawal.registrar = *ctx.accounts.registrar.to_account_info().key;
        pending_withdrawal.locked = locked;

        // Update stake timestamp.
        let member = &mut ctx.accounts.member;
        member.last_stake_ts = ctx.accounts.clock.unix_timestamp;

        Ok(())
    }

    pub fn end_unstake(ctx: Context<EndUnstake>) -> Result<()> {
        if ctx.accounts.pending_withdrawal.end_ts > ctx.accounts.clock.unix_timestamp {
            return Err(ErrorCode::UnstakeTimelock.into());
        }

        // Select which balance set this affects.
        let balances = {
            if ctx.accounts.pending_withdrawal.locked {
                &ctx.accounts.member.balances_locked
            } else {
                &ctx.accounts.member.balances
            }
        };
        // Check the vaults given are corrrect.
        if &balances.vault != ctx.accounts.vault.key {
            return Err(ErrorCode::InvalidVault.into());
        }
        if &balances.vault_pw != ctx.accounts.vault_pw.key {
            return Err(ErrorCode::InvalidVault.into());
        }

        // Transfer tokens between vaults.
        {
            let seeds = &[
                ctx.accounts.registrar.to_account_info().key.as_ref(),
                ctx.accounts.member.to_account_info().key.as_ref(),
                &[ctx.accounts.member.nonce],
            ];
            let signer = &[&seeds[..]];
            let cpi_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.clone(),
                Transfer {
                    from: ctx.accounts.vault_pw.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                    authority: ctx.accounts.member_signer.clone(),
                },
                signer,
            );
            token::transfer(cpi_ctx, ctx.accounts.pending_withdrawal.amount)?;
        }

        // Burn the pending withdrawal receipt.
        let pending_withdrawal = &mut ctx.accounts.pending_withdrawal;
        pending_withdrawal.burned = true;

        Ok(())
    }

    pub fn withdraw(ctx: Context<Withdraw>, amount: u64) -> Result<()> {
        let seeds = &[
            ctx.accounts.registrar.to_account_info().key.as_ref(),
            ctx.accounts.member.to_account_info().key.as_ref(),
            &[ctx.accounts.member.nonce],
        ];
        let signer = &[&seeds[..]];
        let cpi_accounts = Transfer {
            from: ctx.accounts.vault.to_account_info(),
            to: ctx.accounts.depositor.to_account_info(),
            authority: ctx.accounts.member_signer.clone(),
        };
        let cpi_program = ctx.accounts.token_program.clone();
        let cpi_ctx = CpiContext::new_with_signer(cpi_program, cpi_accounts, signer);

        token::transfer(cpi_ctx, amount).map_err(Into::into)
    }

    pub fn withdraw_locked(ctx: Context<WithdrawLocked>, amount: u64) -> Result<()> {
        let seeds = &[
            ctx.accounts.registrar.to_account_info().key.as_ref(),
            ctx.accounts.member.to_account_info().key.as_ref(),
            &[ctx.accounts.member.nonce],
        ];
        let signer = &[&seeds[..]];
        let cpi_accounts = Transfer {
            from: ctx.accounts.member_vault.to_account_info(),
            to: ctx.accounts.vesting_vault.to_account_info(),
            authority: ctx.accounts.member_signer.clone(),
        };
        let cpi_program = ctx.accounts.token_program.clone();
        let cpi_ctx = CpiContext::new_with_signer(cpi_program, cpi_accounts, signer);

        token::transfer(cpi_ctx, amount).map_err(Into::into)
    }

    #[access_control(DropReward::accounts(&ctx, nonce))]
    pub fn drop_reward(
        ctx: Context<DropReward>,
        kind: RewardVendorKind,
        total: u64,
        expiry_ts: i64,
        expiry_receiver: Pubkey,
        nonce: u8,
    ) -> Result<()> {
        if total < ctx.accounts.pool_mint.supply {
            return Err(ErrorCode::InsufficientReward.into());
        }
        if ctx.accounts.clock.unix_timestamp >= expiry_ts {
            return Err(ErrorCode::InvalidExpiry.into());
        }

        // Transfer funds into the vendor's vault.
        token::transfer(ctx.accounts.into(), total)?;

        // Add the event to the reward queue.
        let reward_q = &mut ctx.accounts.reward_event_q;
        let cursor = reward_q.append(RewardEvent {
            vendor: *ctx.accounts.vendor.to_account_info().key,
            ts: ctx.accounts.clock.unix_timestamp,
            locked: kind != RewardVendorKind::Unlocked,
        })?;

        // Initialize the vendor.
        let vendor = &mut ctx.accounts.vendor;
        vendor.registrar = *ctx.accounts.registrar.to_account_info().key;
        vendor.vault = *ctx.accounts.vendor_vault.to_account_info().key;
        vendor.mint = ctx.accounts.vendor_vault.mint;
        vendor.nonce = nonce;
        vendor.pool_token_supply = ctx.accounts.pool_mint.supply;
        vendor.reward_event_q_cursor = cursor;
        vendor.start_ts = ctx.accounts.clock.unix_timestamp;
        vendor.expiry_ts = expiry_ts;
        vendor.expiry_receiver = expiry_receiver;
        vendor.from = *ctx.accounts.depositor_authority.key;
        vendor.total = total;
        vendor.expired = false;
        vendor.kind = kind.clone();

        Ok(())
    }

    #[access_control(reward_eligible(&ctx.accounts.cmn))]
    pub fn claim_reward(ctx: Context<ClaimReward>) -> Result<()> {
        if RewardVendorKind::Unlocked != ctx.accounts.cmn.vendor.kind {
            return Err(ErrorCode::ExpectedUnlockedVendor.into());
        }
        // Reward distribution.
        let spt_total =
            ctx.accounts.cmn.balances.spt.amount + ctx.accounts.cmn.balances_locked.spt.amount;
        let reward_amount = spt_total
            .checked_mul(ctx.accounts.cmn.vendor.total)
            .unwrap()
            .checked_div(ctx.accounts.cmn.vendor.pool_token_supply)
            .unwrap();
        assert!(reward_amount > 0);

        // Send reward to the given token account.
        let seeds = &[
            ctx.accounts.cmn.registrar.to_account_info().key.as_ref(),
            ctx.accounts.cmn.vendor.to_account_info().key.as_ref(),
            &[ctx.accounts.cmn.vendor.nonce],
        ];
        let signer = &[&seeds[..]];
        let cpi_ctx = CpiContext::new_with_signer(
            ctx.accounts.cmn.token_program.clone(),
            token::Transfer {
                from: ctx.accounts.cmn.vault.to_account_info(),
                to: ctx.accounts.to.to_account_info(),
                authority: ctx.accounts.cmn.vendor_signer.to_account_info(),
            },
            signer,
        );
        token::transfer(cpi_ctx, reward_amount)?;

        // Update member as having processed the reward.
        let member = &mut ctx.accounts.cmn.member;
        member.rewards_cursor = ctx.accounts.cmn.vendor.reward_event_q_cursor + 1;

        Ok(())
    }

    #[access_control(reward_eligible(&ctx.accounts.cmn))]
    pub fn claim_reward_locked<'a, 'b, 'c, 'info>(
        ctx: Context<'a, 'b, 'c, 'info, ClaimRewardLocked<'info>>,
        nonce: u8,
    ) -> Result<()> {
        let (end_ts, period_count, schedule) = match ctx.accounts.cmn.vendor.kind {
            RewardVendorKind::Unlocked => return Err(ErrorCode::ExpectedLockedVendor.into()),
            RewardVendorKind::Locked {
                end_ts,
                period_count,
                ref schedule,
            } => (end_ts, period_count, schedule.clone()),
        };

        // Reward distribution.
        let spt_total =
            ctx.accounts.cmn.balances.spt.amount + ctx.accounts.cmn.balances_locked.spt.amount;
        let reward_amount = spt_total
            .checked_mul(ctx.accounts.cmn.vendor.total)
            .unwrap()
            .checked_div(ctx.accounts.cmn.vendor.pool_token_supply)
            .unwrap();
        assert!(reward_amount > 0);

        // The lockup program requires the timestamp to be >= clock's timestamp.
        // So update if the time has already passed.
        //
        // If the reward is within `period_count` seconds of fully vesting, then
        // we bump the `end_ts` because, otherwise, the vesting account would
        // fail to be created. Vesting must have no more frequently than the
        // smallest unit of time, once per second, expressed as
        // `period_count <= end_ts - start_ts`.
        let end_ts = match end_ts < ctx.accounts.cmn.clock.unix_timestamp + period_count as i64 {
            true => ctx.accounts.cmn.clock.unix_timestamp + period_count as i64,
            false => end_ts,
        };

        // Specify the vesting account's realizor, so that unlocks can only
        // execute once completely unstaked.
        let realizor = Some(Realizor {
            program: *ctx.program_id,
            metadata: *ctx.accounts.cmn.member.to_account_info().key,
        });

        // CPI: Create lockup account for the member's beneficiary.
        let seeds = &[
            ctx.accounts.cmn.registrar.to_account_info().key.as_ref(),
            ctx.accounts.cmn.vendor.to_account_info().key.as_ref(),
            &[ctx.accounts.cmn.vendor.nonce],
        ];
        let signer = &[&seeds[..]];
        let mut remaining_accounts: &[AccountInfo] = ctx.remaining_accounts;
        let cpi_program = ctx.accounts.lockup_program.clone();
        let cpi_accounts =
            CreateVesting::try_accounts(ctx.accounts.lockup_program.key, &mut remaining_accounts)?;
        let cpi_ctx = CpiContext::new_with_signer(cpi_program, cpi_accounts, signer);
        lockup::cpi::create_vesting(
            cpi_ctx,
            ctx.accounts.cmn.member.beneficiary,
            end_ts,
            period_count,
            reward_amount,
            nonce,
            realizor,
            schedule.map(Into::into),
        )?;

        // Make sure this reward can't be processed more than once.
        let member = &mut ctx.accounts.cmn.member;
        member.rewards_cursor = ctx.accounts.cmn.vendor.reward_event_q_cursor + 1;

        Ok(())
    }

    pub fn expire_reward(ctx: Context<ExpireReward>) -> Result<()> {
        if ctx.accounts.clock.unix_timestamp < ctx.accounts.vendor.expiry_ts {
            return Err(ErrorCode::VendorNotYetExpired.into());
        }

        // Send all remaining funds to the expiry receiver's token.
        let seeds = &[
            ctx.accounts.registrar.to_account_info().key.as_ref(),
            ctx.accounts.vendor.to_account_info().key.as_ref(),
            &[ctx.accounts.vendor.nonce],
        ];
        let signer = &[&seeds[..]];
        let cpi_ctx = CpiContext::new_with_signer(
            ctx.accounts.token_program.clone(),
            token::Transfer {
                to: ctx.accounts.expiry_receiver_token.to_account_info(),
                from: ctx.accounts.vault.to_account_info(),
                authority: ctx.accounts.vendor_signer.to_account_info(),
            },
            signer,
        );
        token::transfer(cpi_ctx, ctx.accounts.vault.amount)?;

        // Burn the vendor.
        let vendor = &mut ctx.accounts.vendor;
        vendor.expired = true;

        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(init)]
    registrar: ProgramAccount<'info, Registrar>,
    #[account(init)]
    reward_event_q: ProgramAccount<'info, RewardQueue>,
    #[account("pool_mint.decimals == 0")]
    pool_mint: CpiAccount<'info, Mint>,
    rent: Sysvar<'info, Rent>,
}

impl<'info> Initialize<'info> {
    fn accounts(ctx: &Context<Initialize<'info>>, nonce: u8) -> Result<()> {
        let registrar_signer = Pubkey::create_program_address(
            &[
                ctx.accounts.registrar.to_account_info().key.as_ref(),
                &[nonce],
            ],
            ctx.program_id,
        )
        .map_err(|_| ErrorCode::InvalidNonce)?;
        if ctx.accounts.pool_mint.mint_authority != COption::Some(registrar_signer) {
            return Err(ErrorCode::InvalidPoolMintAuthority.into());
        }
        assert!(ctx.accounts.pool_mint.supply == 0);
        Ok(())
    }
}

#[derive(Accounts)]
pub struct UpdateRegistrar<'info> {
    #[account(mut, has_one = authority)]
    registrar: ProgramAccount<'info, Registrar>,
    #[account(signer)]
    authority: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct CreateMember<'info> {
    // Stake instance.
    registrar: ProgramAccount<'info, Registrar>,
    // Member.
    #[account(init)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account(
        "&balances.spt.owner == member_signer.key",
        "balances.spt.mint == registrar.pool_mint",
        "balances.vault.mint == registrar.mint"
    )]
    balances: BalanceSandboxAccounts<'info>,
    #[account(
        "&balances_locked.spt.owner == member_signer.key",
        "balances_locked.spt.mint == registrar.pool_mint",
        "balances_locked.vault.mint == registrar.mint"
    )]
    balances_locked: BalanceSandboxAccounts<'info>,
    member_signer: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    rent: Sysvar<'info, Rent>,
}

impl<'info> CreateMember<'info> {
    fn accounts(ctx: &Context<CreateMember>, nonce: u8) -> Result<()> {
        let seeds = &[
            ctx.accounts.registrar.to_account_info().key.as_ref(),
            ctx.accounts.member.to_account_info().key.as_ref(),
            &[nonce],
        ];
        let member_signer = Pubkey::create_program_address(seeds, ctx.program_id)
            .map_err(|_| ErrorCode::InvalidNonce)?;
        if &member_signer != ctx.accounts.member_signer.to_account_info().key {
            return Err(ErrorCode::InvalidMemberSigner.into());
        }

        Ok(())
    }
}

// When creating a member, the mints and owners of these accounts are correct.
// Upon creation, we assign the accounts. A onetime operation.
// When using a member, we check these accounts addresess are equal to the
// addresses stored on the member. If so, the correct accounts were given are
// correct.
#[derive(Accounts, Clone)]
pub struct BalanceSandboxAccounts<'info> {
    #[account(mut)]
    spt: CpiAccount<'info, TokenAccount>,
    #[account(mut, "vault.owner == spt.owner")]
    vault: CpiAccount<'info, TokenAccount>,
    #[account(
        mut,
        "vault_stake.owner == spt.owner",
        "vault_stake.mint == vault.mint"
    )]
    vault_stake: CpiAccount<'info, TokenAccount>,
    #[account(mut, "vault_pw.owner == spt.owner", "vault_pw.mint == vault.mint")]
    vault_pw: CpiAccount<'info, TokenAccount>,
}

#[derive(Accounts)]
pub struct State<'info> {
    lockup_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct IsRealized<'info> {
    #[account(
        "&member.balances.spt == member_spt.to_account_info().key",
        "&member.balances_locked.spt == member_spt_locked.to_account_info().key"
    )]
    member: ProgramAccount<'info, Member>,
    member_spt: CpiAccount<'info, TokenAccount>,
    member_spt_locked: CpiAccount<'info, TokenAccount>,
}

#[derive(Accounts)]
pub struct UpdateMember<'info> {
    #[account(mut, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct Deposit<'info> {
    // Member.
    #[account(has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account(mut, "vault.to_account_info().key == &member.balances.vault")]
    vault: CpiAccount<'info, TokenAccount>,
    // Depositor.
    #[account(mut)]
    depositor: AccountInfo<'info>,
    #[account(signer, "depositor_authority.key == &member.beneficiary")]
    depositor_authority: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct DepositLocked<'info> {
    // Lockup whitelist relay interface.
    #[account(
        "vesting.to_account_info().owner == &registry.lockup_program",
        "vesting.beneficiary == member.beneficiary"
    )]
    vesting: CpiAccount<'info, Vesting>,
    #[account(mut, "vesting_vault.key == &vesting.vault")]
    vesting_vault: AccountInfo<'info>,
    // Note: no need to verify the depositor_authority since the SPL program
    //       will fail the transaction if it's not correct.
    #[account(signer)]
    depositor_authority: AccountInfo<'info>,
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    #[account(
        mut,
        "member_vault.to_account_info().key == &member.balances_locked.vault"
    )]
    member_vault: CpiAccount<'info, TokenAccount>,
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,

    // Program specific.
    registry: ProgramState<'info, Registry>,
    registrar: ProgramAccount<'info, Registrar>,
    #[account(belongs_to = registrar, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct Stake<'info> {
    // Global accounts for the staking instance.
    #[account(has_one = pool_mint, has_one = reward_event_q)]
    registrar: ProgramAccount<'info, Registrar>,
    reward_event_q: ProgramAccount<'info, RewardQueue>,
    #[account(mut)]
    pool_mint: CpiAccount<'info, Mint>,

    // Member.
    #[account(mut, has_one = beneficiary, belongs_to = registrar)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account("BalanceSandbox::from(&balances) == member.balances")]
    balances: BalanceSandboxAccounts<'info>,
    #[account("BalanceSandbox::from(&balances_locked) == member.balances_locked")]
    balances_locked: BalanceSandboxAccounts<'info>,

    // Program signers.
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,
    #[account(seeds = [registrar.to_account_info().key.as_ref(), &[registrar.nonce]])]
    registrar_signer: AccountInfo<'info>,

    // Misc.
    clock: Sysvar<'info, Clock>,
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct StartUnstake<'info> {
    // Stake instance globals.
    registrar: ProgramAccount<'info, Registrar>,
    reward_event_q: ProgramAccount<'info, RewardQueue>,
    #[account(mut)]
    pool_mint: AccountInfo<'info>,

    // Member.
    #[account(init)]
    pending_withdrawal: ProgramAccount<'info, PendingWithdrawal>,
    #[account(belongs_to = registrar)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account("BalanceSandbox::from(&balances) == member.balances")]
    balances: BalanceSandboxAccounts<'info>,
    #[account("BalanceSandbox::from(&balances_locked) == member.balances_locked")]
    balances_locked: BalanceSandboxAccounts<'info>,

    // Programmatic signers.
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,

    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
    rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct EndUnstake<'info> {
    registrar: ProgramAccount<'info, Registrar>,

    #[account(belongs_to = registrar, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account(mut, belongs_to = registrar, belongs_to = member, "!pending_withdrawal.burned")]
    pending_withdrawal: ProgramAccount<'info, PendingWithdrawal>,

    // if we had ordered maps implementing Accounts we could do a constraint like
    // balances.get(pending_withdrawal.balance_id).vault == vault.key
    #[account(mut)]
    vault: AccountInfo<'info>,
    #[account(mut)]
    vault_pw: AccountInfo<'info>,

    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,

    clock: Sysvar<'info, Clock>,
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct Withdraw<'info> {
    // Stake instance.
    registrar: ProgramAccount<'info, Registrar>,
    // Member.
    #[account(belongs_to = registrar, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account(mut, "vault.to_account_info().key == &member.balances.vault")]
    vault: CpiAccount<'info, TokenAccount>,
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,
    // Receiver.
    #[account(mut)]
    depositor: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct WithdrawLocked<'info> {
    // Lockup whitelist relay interface.
    #[account(
        "vesting.to_account_info().owner == &registry.lockup_program",
        "vesting.beneficiary == member.beneficiary"
    )]
    vesting: CpiAccount<'info, Vesting>,
    #[account(mut, "vesting_vault.key == &vesting.vault")]
    vesting_vault: AccountInfo<'info>,
    #[account(signer)]
    vesting_signer: AccountInfo<'info>,
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    #[account(
        mut,
        "member_vault.to_account_info().key == &member.balances_locked.vault"
    )]
    member_vault: CpiAccount<'info, TokenAccount>,
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            member.to_account_info().key.as_ref(),
            &[member.nonce],
        ]
    )]
    member_signer: AccountInfo<'info>,

    // Program specific.
    registry: ProgramState<'info, Registry>,
    registrar: ProgramAccount<'info, Registrar>,
    #[account(belongs_to = registrar, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct DropReward<'info> {
    // Staking instance.
    #[account(has_one = reward_event_q, has_one = pool_mint)]
    registrar: ProgramAccount<'info, Registrar>,
    #[account(mut)]
    reward_event_q: ProgramAccount<'info, RewardQueue>,
    pool_mint: CpiAccount<'info, Mint>,
    // Vendor.
    #[account(init)]
    vendor: ProgramAccount<'info, RewardVendor>,
    #[account(mut)]
    vendor_vault: CpiAccount<'info, TokenAccount>,
    // Depositor.
    #[account(mut)]
    depositor: AccountInfo<'info>,
    #[account(signer)]
    depositor_authority: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
    rent: Sysvar<'info, Rent>,
}

impl<'info> DropReward<'info> {
    fn accounts(ctx: &Context<DropReward>, nonce: u8) -> Result<()> {
        let vendor_signer = Pubkey::create_program_address(
            &[
                ctx.accounts.registrar.to_account_info().key.as_ref(),
                ctx.accounts.vendor.to_account_info().key.as_ref(),
                &[nonce],
            ],
            ctx.program_id,
        )
        .map_err(|_| ErrorCode::InvalidNonce)?;
        if vendor_signer != ctx.accounts.vendor_vault.owner {
            return Err(ErrorCode::InvalidVaultOwner.into());
        }

        Ok(())
    }
}

#[derive(Accounts)]
pub struct ClaimReward<'info> {
    cmn: ClaimRewardCommon<'info>,
    // Account to send reward to.
    #[account(mut)]
    to: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct ClaimRewardLocked<'info> {
    cmn: ClaimRewardCommon<'info>,
    registry: ProgramState<'info, Registry>,
    #[account("lockup_program.key == &registry.lockup_program")]
    lockup_program: AccountInfo<'info>,
}

// Accounts common to both claim reward locked/unlocked instructions.
#[derive(Accounts)]
pub struct ClaimRewardCommon<'info> {
    // Stake instance.
    registrar: ProgramAccount<'info, Registrar>,
    // Member.
    #[account(mut, belongs_to = registrar, has_one = beneficiary)]
    member: ProgramAccount<'info, Member>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account("BalanceSandbox::from(&balances) == member.balances")]
    balances: BalanceSandboxAccounts<'info>,
    #[account("BalanceSandbox::from(&balances_locked) == member.balances_locked")]
    balances_locked: BalanceSandboxAccounts<'info>,
    // Vendor.
    #[account(belongs_to = registrar, has_one = vault)]
    vendor: ProgramAccount<'info, RewardVendor>,
    #[account(mut)]
    vault: AccountInfo<'info>,
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            vendor.to_account_info().key.as_ref(),
            &[vendor.nonce],
        ]
    )]
    vendor_signer: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
}

#[derive(Accounts)]
pub struct ExpireReward<'info> {
    // Staking instance globals.
    registrar: ProgramAccount<'info, Registrar>,
    // Vendor.
    #[account(mut, belongs_to = registrar, has_one = vault, has_one = expiry_receiver)]
    vendor: ProgramAccount<'info, RewardVendor>,
    #[account(mut)]
    vault: CpiAccount<'info, TokenAccount>,
    #[account(
        seeds = [
            registrar.to_account_info().key.as_ref(),
            vendor.to_account_info().key.as_ref(),
            &[vendor.nonce],
        ]
    )]
    vendor_signer: AccountInfo<'info>,
    // Receiver.
    #[account(signer)]
    expiry_receiver: AccountInfo<'info>,
    #[account(mut)]
    expiry_receiver_token: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
}

#[account]
pub struct Registrar {
    /// Priviledged account.
    pub authority: Pubkey,
    /// Nonce to derive the program-derived address owning the vaults.
    pub nonce: u8,
    /// Number of seconds that must pass for a withdrawal to complete.
    pub withdrawal_timelock: i64,
    /// Global event queue for reward vendoring.
    pub reward_event_q: Pubkey,
    /// Mint of the tokens that can be staked.
    pub mint: Pubkey,
    /// Staking pool token mint.
    pub pool_mint: Pubkey,
    /// The amount of tokens (not decimal) that must be staked to get a single
    /// staking pool token.
    pub stake_rate: u64,
}

#[account]
pub struct Member {
    /// Registrar the member belongs to.
    pub registrar: Pubkey,
    /// The effective owner of the Member account.
    pub beneficiary: Pubkey,
    /// Arbitrary metadata account owned by any program.
    pub metadata: Pubkey,
    /// Sets of balances owned by the Member.
    pub balances: BalanceSandbox,
    /// Locked balances owned by the Member.
    pub balances_locked: BalanceSandbox,
    /// Next position in the rewards event queue to process.
    pub rewards_cursor: u32,
    /// The clock timestamp of the last time this account staked or switched
    /// entities. Used as a proof to reward vendors that the Member account
    /// was staked at a given point in time.
    pub last_stake_ts: i64,
    /// Signer nonce.
    pub nonce: u8,
}

// BalanceSandbox defines isolated funds that can only be deposited/withdrawn
// into the program.
//
// Once controlled by the program, the associated `Member` account's beneficiary
// can send funds to/from any of the accounts within the sandbox, e.g., to
// stake.
#[derive(AnchorSerialize, AnchorDeserialize, Default, Debug, Clone, PartialEq)]
pub struct BalanceSandbox {
    // Staking pool token.
    pub spt: Pubkey,
    // Free balance (deposit) vaults.
    pub vault: Pubkey,
    // Stake vaults.
    pub vault_stake: Pubkey,
    // Pending withdrawal vaults.
    pub vault_pw: Pubkey,
}

#[account]
pub struct PendingWithdrawal {
    /// Registrar this account belongs to.
    pub registrar: Pubkey,
    /// Member this account belongs to.
    pub member: Pubkey,
    /// One time token. True if the withdrawal has been completed.
    pub burned: bool,
    /// The pool being withdrawn from.
    pub pool: Pubkey,
    /// Unix timestamp when this account was initialized.
    pub start_ts: i64,
    /// Timestamp when the pending withdrawal completes.
    pub end_ts: i64,
    /// The number of tokens redeemed from the staking pool.
    pub amount: u64,
    /// True if the withdrawal applies to locked balances.
    pub locked: bool,
}

#[account]
pub struct RewardQueue {
    // Invariant: index is position of the next available slot.
    head: u32,
    // Invariant: index is position of the first (oldest) taken slot.
    // Invariant: head == tail => queue is initialized.
    // Invariant: index_of(head + 1) == index_of(tail) => queue is full.
    tail: u32,
    // Although a vec is used, the size is immutable.
    events: Vec<RewardEvent>,
}

impl RewardQueue {
    pub fn append(&mut self, event: RewardEvent) -> Result<u32> {
        let cursor = self.head;

        // Insert into next available slot.
        let h_idx = self.index_of(self.head);
        self.events[h_idx] = event;

        // Update head and tail counters.
        let is_full = self.index_of(self.head + 1) == self.index_of(self.tail);
        if is_full {
            self.tail += 1;
        }
        self.head += 1;

        Ok(cursor)
    }

    pub fn index_of(&self, counter: u32) -> usize {
        counter as usize % self.capacity()
    }

    pub fn capacity(&self) -> usize {
        self.events.len()
    }

    pub fn get(&self, cursor: u32) -> &RewardEvent {
        &self.events[cursor as usize % self.capacity()]
    }

    pub fn head(&self) -> u32 {
        self.head
    }

    pub fn tail(&self) -> u32 {
        self.tail
    }
}

#[derive(Default, Clone, Copy, Debug, AnchorSerialize, AnchorDeserialize)]
pub struct RewardEvent {
    vendor: Pubkey,
    ts: i64,
    locked: bool,
}

#[account]
pub struct RewardVendor {
    pub registrar: Pubkey,
    pub vault: Pubkey,
    pub mint: Pubkey,
    pub nonce: u8,
    pub pool_token_supply: u64,
    pub reward_event_q_cursor: u32,
    pub start_ts: i64,
    pub expiry_ts: i64,
    pub expiry_receiver: Pubkey,
    pub from: Pubkey,
    pub total: u64,
    pub expired: bool,
    pub kind: RewardVendorKind,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, PartialEq)]
pub enum RewardVendorKind {
    Unlocked,
    Locked {
        end_ts: i64,
        period_count: u64,
        schedule: Option<LockedVendorSchedule>,
    },
}

// Redefine `lockup::Schedule` here since the IDL can't be generate across
// crates (yet).
#[derive(AnchorSerialize, AnchorDeserialize, Clone, PartialEq)]
pub struct LockedVendorSchedule {
    pub program: Pubkey,
    pub metadata: Vec<u8>,
}

impl From<LockedVendorSchedule> for Schedule {
    fn from(s: LockedVendorSchedule) -> Schedule {
        Schedule {
            program: s.program,
            metadata: s.metadata,
        }
    }
}

#[error]
pub enum ErrorCode {
    #[msg("The given reward queue has already been initialized.")]
    RewardQAlreadyInitialized,
    #[msg("The nonce given doesn't derive a valid program address.")]
    InvalidNonce,
    #[msg("Invalid pool mint authority")]
    InvalidPoolMintAuthority,
    #[msg("Member signer doesn't match the derived address.")]
    InvalidMemberSigner,
    #[msg("The given vault owner must match the signing depositor.")]
    InvalidVaultDeposit,
    #[msg("The signing depositor doesn't match either of the balance accounts")]
    InvalidDepositor,
    #[msg("The vault given does not match the vault expected.")]
    InvalidVault,
    #[msg("Invalid vault owner.")]
    InvalidVaultOwner,
    #[msg("An unknown error has occured.")]
    Unknown,
    #[msg("The unstake timelock has not yet expired.")]
    UnstakeTimelock,
    #[msg("Reward vendors must have at least one token unit per pool token")]
    InsufficientReward,
    #[msg("Reward expiry must be after the current clock timestamp.")]
    InvalidExpiry,
    #[msg("The reward vendor has been expired.")]
    VendorExpired,
    #[msg("This reward has already been processed.")]
    CursorAlreadyProcessed,
    #[msg("The account was not staked at the time of this reward.")]
    NotStakedDuringDrop,
    #[msg("The vendor is not yet eligible for expiry.")]
    VendorNotYetExpired,
    #[msg("Please collect your reward before otherwise using the program.")]
    RewardsNeedsProcessing,
    #[msg("Locked reward vendor expected but an unlocked vendor was given.")]
    ExpectedLockedVendor,
    #[msg("Unlocked reward vendor expected but a locked vendor was given.")]
    ExpectedUnlockedVendor,
    #[msg("Locked deposit from an invalid deposit authority.")]
    InvalidVestingSigner,
    #[msg("Locked rewards cannot be realized until one unstaked all tokens.")]
    UnrealizedReward,
    #[msg("The beneficiary doesn't match.")]
    InvalidBeneficiary,
    #[msg("The given member account does not match the realizor metadata.")]
    InvalidRealizorMetadata,
}

impl<'a, 'b, 'c, 'info> From<&mut Deposit<'info>>
    for CpiContext<'a, 'b, 'c, 'info, Transfer<'info>>
{
    fn from(accounts: &mut Deposit<'info>) -> CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            from: accounts.depositor.clone(),
            to: accounts.vault.to_account_info(),
            authority: accounts.depositor_authority.clone(),
        };
        let cpi_program = accounts.token_program.clone();
        CpiContext::new(cpi_program, cpi_accounts)
    }
}

impl<'a, 'b, 'c, 'info> From<&mut DepositLocked<'info>>
    for CpiContext<'a, 'b, 'c, 'info, Transfer<'info>>
{
    fn from(accounts: &mut DepositLocked<'info>) -> CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            from: accounts.vesting_vault.clone(),
            to: accounts.member_vault.to_account_info(),
            authority: accounts.depositor_authority.clone(),
        };
        let cpi_program = accounts.token_program.clone();
        CpiContext::new(cpi_program, cpi_accounts)
    }
}

impl<'a, 'b, 'c, 'info> From<&mut DropReward<'info>>
    for CpiContext<'a, 'b, 'c, 'info, Transfer<'info>>
{
    fn from(accounts: &mut DropReward<'info>) -> CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            from: accounts.depositor.clone(),
            to: accounts.vendor_vault.to_account_info(),
            authority: accounts.depositor_authority.clone(),
        };
        let cpi_program = accounts.token_program.clone();
        CpiContext::new(cpi_program, cpi_accounts)
    }
}

impl<'info> From<&BalanceSandboxAccounts<'info>> for BalanceSandbox {
    fn from(accs: &BalanceSandboxAccounts<'info>) -> Self {
        Self {
            spt: *accs.spt.to_account_info().key,
            vault: *accs.vault.to_account_info().key,
            vault_stake: *accs.vault_stake.to_account_info().key,
            vault_pw: *accs.vault_pw.to_account_info().key,
        }
    }
}

fn reward_eligible(cmn: &ClaimRewardCommon) -> Result<()> {
    let vendor = &cmn.vendor;
    let member = &cmn.member;
    if vendor.expired {
        return Err(ErrorCode::VendorExpired.into());
    }
    if member.rewards_cursor > vendor.reward_event_q_cursor {
        return Err(ErrorCode::CursorAlreadyProcessed.into());
    }
    if member.last_stake_ts > vendor.start_ts {
        return Err(ErrorCode::NotStakedDuringDrop.into());
    }
    Ok(())
}

// Asserts the user calling the `Stake` instruction has no rewards available
// in the reward queue.
pub fn no_available_rewards<'info>(
    reward_q: &ProgramAccount<'info, RewardQueue>,
    member: &ProgramAccount<'info, Member>,
    balances: &BalanceSandboxAccounts<'info>,
    balances_locked: &BalanceSandboxAccounts<'info>,
) -> Result<()> {
    let mut cursor = member.rewards_cursor;

    // If the member's cursor is less then the tail, then the ring buffer has
    // overwritten those entries, so jump to the tail.
    let tail = reward_q.tail();
    if cursor < tail {
        cursor = tail;
    }

    while cursor < reward_q.head() {
        let r_event = reward_q.get(cursor);
        if member.last_stake_ts < r_event.ts {
            if balances.spt.amount > 0 || balances_locked.spt.amount > 0 {
                return Err(ErrorCode::RewardsNeedsProcessing.into());
            }
        }
        cursor += 1;
    }

    Ok(())
}
