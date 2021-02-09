//! counter-auth is an example of a program *implementing* an external program
//! interface. Here the `counter::Auth` trait, where we only allow a count
//! to be incremented if it changes the counter from odd -> even or even -> odd.
//! Creative, I know. :P.

#![feature(proc_macro_hygiene)]

use anchor_lang::prelude::*;
use counter::Auth;

#[program]
pub mod counter_auth {
    use super::*;

    #[state]
    pub struct CounterAuth;

    impl<'info> Auth<'info, Empty> for CounterAuth {
        fn is_authorized(_ctx: Context<Empty>, current: u64, new: u64) -> ProgramResult {
            if current % 2 == 0 {
                if new % 2 == 0 {
                    return Err(ProgramError::Custom(50)); // Arbitrary error code.
                }
            } else {
                if new % 2 == 1 {
                    return Err(ProgramError::Custom(60)); // Arbitrary error code.
                }
            }
            Ok(())
        }
    }
}

#[derive(Accounts)]
pub struct Empty {}
