//! Linear is a vesting schedule function that can plug into the lockup program.
//! Vesting occurs linearly from the given schedule's `start_ts` to the
//! schedule's `end_ts`, `period_count` times.

#![feature(proc_macro_hygiene)]

use anchor_lang::prelude::*;
use anchor_spl::shmem;
use lockup::{Vesting, VestingSchedule};

// MARK: Program.

#[program]
pub mod linear {
    use super::*;

    #[state]
    pub struct Linear;

    impl<'info> VestingSchedule<'info, TotalVested<'info>> for Linear {
        fn total_vested(ctx: Context<TotalVested>, v: Vesting, current_ts: i64) -> ProgramResult {
            // Calculate linear unlack.
            let vested_amount = {
                if current_ts < ctx.accounts.schedule.start_ts {
                    0
                } else if current_ts >= ctx.accounts.schedule.end_ts {
                    v.start_balance
                } else {
                    linear_unlock(&v, &ctx.accounts.schedule, current_ts).unwrap()
                }
            };
            // Write the return value for the CPI caller.
            let cpi_ctx = CpiContext::new(
                ctx.accounts.shmem_program.clone(),
                shmem::Ret::new(ctx.accounts.shmem.clone()),
            );
            shmem::ret(cpi_ctx, vested_amount.to_le_bytes().to_vec())?;

            Ok(())
        }
    }

    pub fn create_schedule(
        ctx: Context<CreateSchedule>,
        start_ts: i64,
        end_ts: i64,
        period_count: u64,
    ) -> Result<()> {
        if end_ts <= start_ts {
            return Err(ErrorCode::InvalidTimestamp.into());
        }
        if period_count > (end_ts - start_ts) as u64 {
            return Err(ErrorCode::InvalidPeriod.into());
        }
        if period_count == 0 {
            return Err(ErrorCode::InvalidPeriod.into());
        }

        let schedule = &mut ctx.accounts.schedule;
        schedule.start_ts = start_ts;
        schedule.end_ts = end_ts;
        schedule.period_count = period_count;

        Ok(())
    }
}

// MARK: Accounts.

#[derive(Accounts)]
pub struct CreateSchedule<'info> {
    #[account(init)]
    schedule: ProgramAccount<'info, Schedule>,
    rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct TotalVested<'info> {
    schedule: ProgramAccount<'info, Schedule>,
    #[account(mut, "shmem.owner == shmem_program.key")]
    pub shmem: AccountInfo<'info>,
    #[account("shmem_program.key == &shmem::ID")]
    pub shmem_program: AccountInfo<'info>,
}

#[account]
pub struct Schedule {
    /// The time at which vesting begins.
    start_ts: i64,
    /// The time at which all tokens are vested.
    end_ts: i64,
    /// The number of times vesting will occur. For example, if vesting
    /// is once a year over seven years, this will be 7.
    period_count: u64,
}

// MARK: Error.

#[error]
pub enum ErrorCode {
    #[msg("Vesting end must be greater than the current unix timestamp.")]
    InvalidTimestamp,
    #[msg("The number of vesting periods must be greater than zero.")]
    InvalidPeriod,
}

// MARK: Vesting function.

// Returns the total vested amount up to the `current_ts`.
fn linear_unlock(vesting: &Vesting, schedule: &Schedule, current_ts: i64) -> Option<u64> {
    // Signed division not supported.
    let current_ts = current_ts as u64;
    let start_ts = schedule.start_ts as u64;
    let end_ts = schedule.end_ts as u64;

    // If we can't perfectly partition the vesting window,
    // push the start of the window back so that we can.
    //
    // This has the effect of making the first vesting period shorter
    // than the rest.
    let shifted_start_ts =
        start_ts.checked_sub(end_ts.checked_sub(start_ts)? % schedule.period_count)?;

    // Similarly, if we can't perfectly divide up the vesting rewards
    // then make the first period act as a cliff, earning slightly more than
    // subsequent periods.
    let reward_overflow = vesting.start_balance % schedule.period_count;

    // Reward per period ignoring the overflow.
    let reward_per_period =
        (vesting.start_balance.checked_sub(reward_overflow)?).checked_div(schedule.period_count)?;

    // Number of vesting periods that have passed.
    let current_period = {
        let period_secs =
            (end_ts.checked_sub(shifted_start_ts)?).checked_div(schedule.period_count)?;
        let current_period_count =
            (current_ts.checked_sub(shifted_start_ts)?).checked_div(period_secs)?;
        std::cmp::min(current_period_count, schedule.period_count)
    };

    if current_period == 0 {
        return Some(0);
    }

    current_period
        .checked_mul(reward_per_period)?
        .checked_add(reward_overflow)
}
