//! CPI API for interacting with the SPL shared memory
//! [program](https://github.com/solana-labs/solana-program-library/tree/master/shared-memory).

use anchor_lang::{Accounts, CpiContext};
use solana_program::account_info::AccountInfo;
use solana_program::declare_id;
use solana_program::entrypoint::ProgramResult;
use solana_program::instruction::{AccountMeta, Instruction};
use solana_program::program;

// TODO: update this once the final shared memory program gets released.
//       shmem4EWT2sPdVGvTZCzXXRAURL9G5vpPxNwSeKhHUL.
declare_id!("DynWy94wrWp5RimU49creYMQ5py3Up8BBNS4VA73VCpi");

/// `ret` writes the given `data` field to the shared memory account
/// acting as a return value that can be used across CPI.
/// The caleee should use this to write data into the shared memory account.
/// The caler should use the account directly to pull out and interpret the
/// bytes. Shared memory serialization is not specified and is up to the
/// caller and callee.
pub fn ret<'a, 'b, 'c, 'info>(
    ctx: CpiContext<'a, 'b, 'c, 'info, Ret<'info>>,
    data: Vec<u8>,
) -> ProgramResult {
    let instruction = Instruction {
        program_id: *ctx.program.key,
        accounts: vec![AccountMeta::new(*ctx.accounts.buffer.key, false)],
        data,
    };
    let mut accounts = vec![ctx.accounts.buffer];
    accounts.push(ctx.program.clone());
    program::invoke(&instruction, &accounts)
}

#[derive(Accounts)]
pub struct Ret<'info> {
    #[account(mut)]
    pub buffer: AccountInfo<'info>,
}

impl<'info> Ret<'info> {
    pub fn new(buffer: AccountInfo<'info>) -> Self {
        Self { buffer }
    }
}

// A set of accounts that can be used with shared memory.
#[derive(Accounts)]
pub struct Shmem<'info> {
    // Shared memory account to write the return value into.
    #[account(mut, "shmem.owner == shmem_program.key")]
    pub shmem: AccountInfo<'info>,
    #[account("shmem_program.key == &ID")]
    pub shmem_program: AccountInfo<'info>,
}
