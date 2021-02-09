//! Cliff is a vesting schedule function that can plug into the lockup
//! program. Vesting occurs linearly *after* the vesting account's
//! start date + its offset.

#![feature(proc_macro_hygiene)]

use anchor_lang::prelude::*;
use anchor_spl::shmem::{self, Shmem};
use lockup::{calculator, Vesting, VestingSchedule};

#[program]
pub mod cliff {
    use super::*;

    #[state]
    pub struct Cliff;

    impl VestingSchedule for Cliff {
        fn available_for_withdrawal(
            ctx: Context<Shmem>,
            v: Vesting,
            current_ts: i64,
        ) -> ProgramResult {
            // Shift start date forward a year.
            let mut v = v;
            v.start_ts += 60 * 60 * 24 * 365;

            // Calculate linear unlack.
            let available = calculator::available_for_withdrawal(&v, current_ts);

            // Write the return value for the CPI caller.
            let cpi_ctx = CpiContext::new(
                ctx.accounts.shmem_program.clone(),
                shmem::Ret::new(ctx.accounts.shmem.clone()),
            );
            shmem::ret(cpi_ctx, available.to_le_bytes().to_vec())?;

            Ok(())
        }
    }
}
