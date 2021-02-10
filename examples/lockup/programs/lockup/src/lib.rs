//! A relatively advanced example of a lockup program. If you're new to Anchor,
//! it's suggested to start with the other examples.

#![feature(proc_macro_hygiene)]

use anchor_lang::prelude::*;
use anchor_lang::solana_program::instruction::Instruction;
use anchor_lang::solana_program::program;
use anchor_spl::shmem;
use anchor_spl::token::{self, TokenAccount, Transfer};

// MARK: Program.

#[program]
pub mod lockup {
    use super::*;

    #[state]
    pub struct Lockup {
        /// The key with the ability to change the whitelist.
        pub authority: Pubkey,
        /// List of programs locked tokens can be sent to. These programs
        /// are completely trusted to maintain the locked property.
        pub whitelist: Vec<WhitelistEntry>,
    }

    impl Lockup {
        pub const WHITELIST_SIZE: usize = 10;

        pub fn new(ctx: Context<Auth>) -> Result<Self> {
            let mut whitelist = vec![];
            whitelist.resize(Self::WHITELIST_SIZE, Default::default());
            Ok(Lockup {
                authority: *ctx.accounts.authority.key,
                whitelist,
            })
        }

        #[access_control(whitelist_auth(self, &ctx))]
        pub fn whitelist_add(&mut self, ctx: Context<Auth>, entry: WhitelistEntry) -> Result<()> {
            if self.whitelist.len() == Self::WHITELIST_SIZE {
                return Err(ErrorCode::WhitelistFull.into());
            }
            if self.whitelist.contains(&entry) {
                return Err(ErrorCode::WhitelistEntryAlreadyExists.into());
            }
            self.whitelist.push(entry);
            Ok(())
        }

        #[access_control(whitelist_auth(self, &ctx))]
        pub fn whitelist_delete(
            &mut self,
            ctx: Context<Auth>,
            entry: WhitelistEntry,
        ) -> Result<()> {
            if !self.whitelist.contains(&entry) {
                return Err(ErrorCode::WhitelistEntryNotFound.into());
            }
            self.whitelist.retain(|e| e != &entry);
            Ok(())
        }

        #[access_control(whitelist_auth(self, &ctx))]
        pub fn set_authority(&mut self, ctx: Context<Auth>, new_authority: Pubkey) -> Result<()> {
            self.authority = new_authority;
            Ok(())
        }
    }

    #[access_control(CreateVesting::accounts(&ctx, nonce))]
    pub fn create_vesting(
        ctx: Context<CreateVesting>,
        beneficiary: Pubkey,
        deposit_amount: u64,
        nonce: u8,
        schedule: Ext,
        realizor: Option<Ext>,
    ) -> Result<()> {
        if deposit_amount == 0 {
            return Err(ErrorCode::InvalidDepositAmount.into());
        }

        let vesting = &mut ctx.accounts.vesting;
        vesting.beneficiary = beneficiary;
        vesting.mint = ctx.accounts.vault.mint;
        vesting.vault = *ctx.accounts.vault.to_account_info().key;
        vesting.start_balance = deposit_amount;
        vesting.created_ts = ctx.accounts.clock.unix_timestamp;
        vesting.outstanding = deposit_amount;
        vesting.whitelist_owned = 0;
        vesting.grantor = *ctx.accounts.depositor_authority.key;
        vesting.nonce = nonce;
        vesting.schedule = schedule;
        vesting.realizor = realizor;

        token::transfer(ctx.accounts.into(), deposit_amount)?;

        Ok(())
    }

    #[access_control(
        is_realized(&ctx)
        is_withdrawable(&ctx, amount)
    )]
    pub fn withdraw<'a, 'b, 'c, 'info>(
        ctx: Context<'a, 'b, 'c, 'info, Withdraw<'info>>,
        amount: u64,
    ) -> Result<()> {
        // Transfer funds out.
        let seeds = &[
            ctx.accounts.vesting.to_account_info().key.as_ref(),
            &[ctx.accounts.vesting.nonce],
        ];
        let signer = &[&seeds[..]];
        let cpi_ctx = CpiContext::from(&*ctx.accounts).with_signer(signer);
        token::transfer(cpi_ctx, amount)?;

        // Bookeeping.
        let vesting = &mut ctx.accounts.vesting;
        vesting.outstanding -= amount;

        Ok(())
    }

    // Sends funds from the lockup program to a whitelisted program.
    pub fn whitelist_withdraw<'a, 'b, 'c, 'info>(
        ctx: Context<'a, 'b, 'c, 'info, WhitelistWithdraw<'info>>,
        instruction_data: Vec<u8>,
        amount: u64,
    ) -> Result<()> {
        let before_amount = ctx.accounts.transfer.vault.amount;
        whitelist_relay_cpi(
            &ctx.accounts.transfer,
            ctx.remaining_accounts,
            instruction_data,
        )?;
        let after_amount = ctx.accounts.transfer.vault.reload()?.amount;

        // CPI safety checks.
        let withdraw_amount = before_amount - after_amount;
        if withdraw_amount > amount {
            return Err(ErrorCode::WhitelistWithdrawLimit)?;
        }

        // Bookeeping.
        ctx.accounts.transfer.vesting.whitelist_owned += withdraw_amount;

        Ok(())
    }

    // Sends funds from a whitelisted program back to the lockup program.
    pub fn whitelist_deposit<'a, 'b, 'c, 'info>(
        ctx: Context<'a, 'b, 'c, 'info, WhitelistDeposit<'info>>,
        instruction_data: Vec<u8>,
    ) -> Result<()> {
        let before_amount = ctx.accounts.transfer.vault.amount;
        whitelist_relay_cpi(
            &ctx.accounts.transfer,
            ctx.remaining_accounts,
            instruction_data,
        )?;
        let after_amount = ctx.accounts.transfer.vault.reload()?.amount;

        // CPI safety checks.
        let deposit_amount = after_amount - before_amount;
        if deposit_amount <= 0 {
            return Err(ErrorCode::InsufficientWhitelistDepositAmount)?;
        }
        if deposit_amount > ctx.accounts.transfer.vesting.whitelist_owned {
            return Err(ErrorCode::WhitelistDepositOverflow)?;
        }

        // Bookkeeping.
        ctx.accounts.transfer.vesting.whitelist_owned -= deposit_amount;

        Ok(())
    }

    // Convenience function for UI's to calculate the withdrawable amount.
    pub fn available_for_withdrawal<'a, 'b, 'c, 'info>(
        ctx: Context<'a, 'b, 'c, 'info, AvailableForWithdrawal<'info>>,
    ) -> Result<()> {
        let available = withdrawable(
            &ctx.accounts.vesting,
            &ctx.accounts.clock,
            &ctx.accounts.schedule,
        )?;
        // Log as string so that JS can read as a BN.
        msg!(&format!("{{ \"result\": \"{}\" }}", available));
        Ok(())
    }
}

// MARK: Accounts.

#[derive(Accounts)]
pub struct Auth<'info> {
    #[account(signer)]
    authority: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct CreateVesting<'info> {
    // Vesting.
    #[account(init)]
    vesting: ProgramAccount<'info, Vesting>,
    #[account(mut)]
    vault: CpiAccount<'info, TokenAccount>,
    // Depositor.
    #[account(mut)]
    depositor: AccountInfo<'info>,
    #[account(signer)]
    depositor_authority: AccountInfo<'info>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    rent: Sysvar<'info, Rent>,
    clock: Sysvar<'info, Clock>,
}

impl<'info> CreateVesting<'info> {
    fn accounts(ctx: &Context<CreateVesting>, nonce: u8) -> Result<()> {
        let vault_authority = Pubkey::create_program_address(
            &[
                ctx.accounts.vesting.to_account_info().key.as_ref(),
                &[nonce],
            ],
            ctx.program_id,
        )
        .map_err(|_| ErrorCode::InvalidProgramAddress)?;
        if ctx.accounts.vault.owner != vault_authority {
            return Err(ErrorCode::InvalidVaultOwner)?;
        }

        Ok(())
    }
}

// All accounts not included here, i.e., the "remaining accounts" should be
// ordered according to the realization interface.
#[derive(Accounts)]
pub struct Withdraw<'info> {
    // Vesting.
    #[account(mut, has_one = beneficiary, has_one = vault)]
    vesting: ProgramAccount<'info, Vesting>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    #[account(mut)]
    vault: CpiAccount<'info, TokenAccount>,
    #[account(seeds = [vesting.to_account_info().key.as_ref(), &[vesting.nonce]])]
    vesting_signer: AccountInfo<'info>,
    // Withdraw receiving target..
    #[account(mut)]
    token: CpiAccount<'info, TokenAccount>,
    // Misc.
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
    #[account(
        "&vesting.schedule.program == schedule.program.key",
        "&vesting.schedule.metadata == schedule.metadata.key"
    )]
    schedule: Schedule<'info>,
}

#[derive(Accounts)]
pub struct Schedule<'info> {
    program: AccountInfo<'info>,
    metadata: AccountInfo<'info>,
    #[account(mut, "shmem.owner == shmem_program.key")]
    shmem: AccountInfo<'info>,
    #[account("shmem_program.key == &shmem::ID")]
    shmem_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct WhitelistWithdraw<'info> {
    transfer: WhitelistTransfer<'info>,
}

#[derive(Accounts)]
pub struct WhitelistDeposit<'info> {
    transfer: WhitelistTransfer<'info>,
}

#[derive(Accounts)]
pub struct WhitelistTransfer<'info> {
    lockup: ProgramState<'info, Lockup>,
    #[account(signer)]
    beneficiary: AccountInfo<'info>,
    whitelisted_program: AccountInfo<'info>,

    // Whitelist interface.
    #[account(mut, has_one = beneficiary, has_one = vault)]
    vesting: ProgramAccount<'info, Vesting>,
    #[account(mut, "&vault.owner == vesting_signer.key")]
    vault: CpiAccount<'info, TokenAccount>,
    #[account(seeds = [vesting.to_account_info().key.as_ref(), &[vesting.nonce]])]
    vesting_signer: AccountInfo<'info>,
    #[account("token_program.key == &token::ID")]
    token_program: AccountInfo<'info>,
    #[account(mut)]
    whitelisted_program_vault: AccountInfo<'info>,
    whitelisted_program_vault_authority: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct AvailableForWithdrawal<'info> {
    vesting: ProgramAccount<'info, Vesting>,
    clock: Sysvar<'info, Clock>,
    schedule: Schedule<'info>,
}

#[account]
pub struct Vesting {
    /// The owner of this Vesting account.
    pub beneficiary: Pubkey,
    /// The mint of the SPL token locked up.
    pub mint: Pubkey,
    /// The owner of the token account funding this account.
    pub grantor: Pubkey,
    /// Address of the account's token vault.
    pub vault: Pubkey,
    /// The outstanding SRM deposit backing this vesting account. All
    /// withdrawals will deduct this balance.
    pub outstanding: u64,
    /// The starting balance of this vesting account, i.e., how much was
    /// originally deposited.
    pub start_balance: u64,
    /// The unix timestamp at which this vesting account was created.
    pub created_ts: i64,
    /// The amount of tokens in custody of whitelisted programs.
    pub whitelist_owned: u64,
    /// Signer nonce.
    pub nonce: u8,
    /// External program defining a vesting schedule.
    pub schedule: Ext,
    /// External program defining a "realization" condition.
    ///
    /// In addition to the lockup schedule, the program provides the ability
    /// for applications to determine when locked tokens are considered earned.
    /// For example, when earning locked tokens via the staking program, one
    /// cannot receive the tokens until unstaking. As a result, if one never
    /// unstakes, one would never actually receive the locked tokens.
    pub realizor: Option<Ext>,
}

/// An external program and account state. For example, this could be the
/// staking `Registry` program and a `Member` account.
#[derive(AnchorSerialize, AnchorDeserialize, Clone, Debug)]
pub struct Ext {
    /// External program id to invoke.
    pub program: Pubkey,
    /// Address of an arbitrary piece of metadata interpretable by the external
    /// program.
    ///
    /// For example, when a vesting account is allocated, the program can define
    /// its realization condition as a function of some account state. The
    /// metadata is the address of that account.
    ///
    /// In the case of staking, the metadata is a `Member` account address. When
    /// the realization condition is checked, the staking program will check the
    /// `Member` account defined by the `metadata` has no staked tokens.
    pub metadata: Pubkey,
}

#[derive(AnchorSerialize, AnchorDeserialize, PartialEq, Default, Copy, Clone)]
pub struct WhitelistEntry {
    pub program_id: Pubkey,
}

// MARK: Error.

#[error]
pub enum ErrorCode {
    #[msg("The vesting deposit amount must be greater than zero.")]
    InvalidDepositAmount,
    #[msg("The Whitelist entry is not a valid program address.")]
    InvalidWhitelistEntry,
    #[msg("Invalid program address. Did you provide the correct nonce?")]
    InvalidProgramAddress,
    #[msg("Invalid vault owner.")]
    InvalidVaultOwner,
    #[msg("Vault amount must be zero.")]
    InvalidVaultAmount,
    #[msg("Insufficient withdrawal balance.")]
    InsufficientWithdrawalBalance,
    #[msg("Whitelist is full")]
    WhitelistFull,
    #[msg("Whitelist entry already exists")]
    WhitelistEntryAlreadyExists,
    #[msg("Balance must go up when performing a whitelist deposit")]
    InsufficientWhitelistDepositAmount,
    #[msg("Cannot deposit more than withdrawn")]
    WhitelistDepositOverflow,
    #[msg("Tried to withdraw over the specified limit")]
    WhitelistWithdrawLimit,
    #[msg("Whitelist entry not found.")]
    WhitelistEntryNotFound,
    #[msg("You do not have sufficient permissions to perform this action.")]
    Unauthorized,
    #[msg("You are unable to realize projected rewards until unstaking.")]
    UnableToWithdrawWhileStaked,
    #[msg("The given lock realizor doesn't match the vesting account.")]
    InvalidLockRealizor,
    #[msg("You have not realized this vesting account.")]
    UnrealizedVesting,
    #[msg("The given vesting schedule program is invalid.")]
    InvalidScheduleProgram,
}

// MARK: From impls.

impl<'a, 'b, 'c, 'info> From<&mut CreateVesting<'info>>
    for CpiContext<'a, 'b, 'c, 'info, Transfer<'info>>
{
    fn from(accounts: &mut CreateVesting<'info>) -> CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            from: accounts.depositor.clone(),
            to: accounts.vault.to_account_info(),
            authority: accounts.depositor_authority.clone(),
        };
        let cpi_program = accounts.token_program.clone();
        CpiContext::new(cpi_program, cpi_accounts)
    }
}

impl<'a, 'b, 'c, 'info> From<&Withdraw<'info>> for CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
    fn from(accounts: &Withdraw<'info>) -> CpiContext<'a, 'b, 'c, 'info, Transfer<'info>> {
        let cpi_accounts = Transfer {
            from: accounts.vault.to_account_info(),
            to: accounts.token.to_account_info(),
            authority: accounts.vesting_signer.to_account_info(),
        };
        let cpi_program = accounts.token_program.to_account_info();
        CpiContext::new(cpi_program, cpi_accounts)
    }
}

// MARK: Access control modifiers.

pub fn is_whitelisted<'info>(transfer: &WhitelistTransfer<'info>) -> Result<()> {
    if !transfer.lockup.whitelist.contains(&WhitelistEntry {
        program_id: *transfer.whitelisted_program.key,
    }) {
        return Err(ErrorCode::WhitelistEntryNotFound.into());
    }
    Ok(())
}

fn whitelist_auth(lockup: &Lockup, ctx: &Context<Auth>) -> Result<()> {
    if &lockup.authority != ctx.accounts.authority.key {
        return Err(ErrorCode::Unauthorized.into());
    }
    Ok(())
}

// Returns Ok if the locked vesting account has been "realized". Realization
// is application dependent. For example, in the case of staking, one must first
// unstake before being able to earn locked tokens.
fn is_realized(ctx: &Context<Withdraw>) -> Result<()> {
    if let Some(realizor) = &ctx.accounts.vesting.realizor {
        let cpi_program = {
            let p = ctx.remaining_accounts[0].clone();
            if p.key != &realizor.program {
                return Err(ErrorCode::InvalidLockRealizor.into());
            }
            p
        };
        let cpi_accounts = ctx.remaining_accounts.to_vec()[1..].to_vec();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);
        let vesting = (*ctx.accounts.vesting).clone();
        realize_lock::is_realized(cpi_ctx, vesting).map_err(|_| ErrorCode::UnrealizedVesting)?;
    }
    Ok(())
}

// Returns Ok if the vesting account can withdraw the given amount, irrespective
// of realization.
fn is_withdrawable<'a, 'b, 'c, 'info>(
    ctx: &Context<'a, 'b, 'c, 'info, Withdraw<'info>>,
    amount: u64,
) -> Result<()> {
    let withdrawable_amount = withdrawable(
        &ctx.accounts.vesting,
        &ctx.accounts.clock,
        &ctx.accounts.schedule,
    )?;
    if amount > withdrawable_amount {
        return Err(ErrorCode::InsufficientWithdrawalBalance.into());
    }
    Ok(())
}

// MARK: Helpers.

#[access_control(is_whitelisted(transfer))]
pub fn whitelist_relay_cpi<'info>(
    transfer: &WhitelistTransfer<'info>,
    remaining_accounts: &[AccountInfo<'info>],
    instruction_data: Vec<u8>,
) -> Result<()> {
    let mut meta_accounts = vec![
        AccountMeta::new_readonly(*transfer.vesting.to_account_info().key, false),
        AccountMeta::new(*transfer.vault.to_account_info().key, false),
        AccountMeta::new_readonly(*transfer.vesting_signer.to_account_info().key, true),
        AccountMeta::new_readonly(*transfer.token_program.to_account_info().key, false),
        AccountMeta::new(
            *transfer.whitelisted_program_vault.to_account_info().key,
            false,
        ),
        AccountMeta::new_readonly(
            *transfer
                .whitelisted_program_vault_authority
                .to_account_info()
                .key,
            false,
        ),
    ];
    meta_accounts.extend(remaining_accounts.iter().map(|a| {
        if a.is_writable {
            AccountMeta::new(*a.key, a.is_signer)
        } else {
            AccountMeta::new_readonly(*a.key, a.is_signer)
        }
    }));
    let relay_instruction = Instruction {
        program_id: *transfer.whitelisted_program.to_account_info().key,
        accounts: meta_accounts,
        data: instruction_data.to_vec(),
    };

    let seeds = &[
        transfer.vesting.to_account_info().key.as_ref(),
        &[transfer.vesting.nonce],
    ];
    let signer = &[&seeds[..]];
    let mut accounts = transfer.to_account_infos();
    accounts.extend_from_slice(&remaining_accounts);
    program::invoke_signed(&relay_instruction, &accounts, signer).map_err(Into::into)
}

fn withdrawable<'a, 'info>(
    vesting: &ProgramAccount<'info, Vesting>,
    clock: &Sysvar<'info, Clock>,
    schedule: &Schedule<'info>,
) -> Result<u64> {
    let current_balance = balance(&*vesting);
    let vested_outstanding = outstanding_vested(vesting, clock, schedule)?;
    Ok(std::cmp::min(current_balance, vested_outstanding))
}

// The amount of funds currently in the vault.
fn balance(vesting: &Vesting) -> u64 {
    vesting
        .outstanding
        .checked_sub(vesting.whitelist_owned)
        .unwrap()
}

// The amount of outstanding locked tokens vested. Note that these
// tokens might have been transferred to whitelisted programs, so this amount
// can be less than what is actually in the vault.
fn outstanding_vested<'a, 'info>(
    vesting: &ProgramAccount<'info, Vesting>,
    clock: &Sysvar<'info, Clock>,
    schedule: &Schedule<'info>,
) -> Result<u64> {
    let total_vested = {
        // Invoke external program to calculate the withdrawable amount.
        let cpi_accounts = schedule.to_account_infos()[1..].to_vec();
        let cpi_ctx = CpiContext::new(schedule.program.clone(), cpi_accounts);
        vesting_schedule::total_vested(cpi_ctx, (**vesting).clone(), clock.unix_timestamp)?;

        // Decode the CPI return value.
        let shmem = &schedule.shmem;
        let mut result = [0u8; 8];
        result.copy_from_slice(&shmem.try_borrow_data()?[..]);
        u64::from_le_bytes(result)
    };

    Ok(total_vested
        .checked_sub(withdrawn_amount(&vesting))
        .unwrap())
}

// Returns the amount withdrawn from this vesting account.
fn withdrawn_amount(vesting: &Vesting) -> u64 {
    vesting
        .start_balance
        .checked_sub(vesting.outstanding)
        .unwrap()
}

// MARK: External program interfaces.

/// RealizeLock defines the interface an external program must implement if
/// they want to define a "realization condition" on a locked vesting account.
/// This condition must be satisfied *even if a vesting schedule has
/// completed*. Otherwise the user can never earn the locked funds. For example,
/// in the case of the staking program, one cannot received a locked reward
/// until one has completely unstaked.
#[interface]
pub trait RealizeLock<'info, T: Accounts<'info>> {
    fn is_realized(ctx: Context<T>, v: Vesting) -> ProgramResult;
}

/// Vesting schedule defines the interface an external program must implement
/// if they want to define a custom vesting schedule function.
#[interface]
pub trait VestingSchedule<'info, T: Accounts<'info>> {
    /// Returns the amount vested up tlil the given `current_ts`.
    fn total_vested(ctx: Context<T>, v: Vesting, current_ts: i64) -> ProgramResult;
}
