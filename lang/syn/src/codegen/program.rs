use crate::parser;
use crate::{Program, RpcArg, State};
use heck::{CamelCase, SnakeCase};
use quote::quote;

// Namespace for calculating state instruction sighash signatures.
const SIGHASH_STATE_NAMESPACE: &'static str = "state";

// Namespace for calculating instruction sighash signatures for any instruction
// not affecting program state.
const SIGHASH_GLOBAL_NAMESPACE: &'static str = "global";

pub fn generate(program: Program) -> proc_macro2::TokenStream {
    let mod_name = &program.name;
    let dispatch = generate_dispatch(&program);
    let handlers_non_inlined = generate_non_inlined_handlers(&program);
    let methods = generate_methods(&program);
    let instructions = generate_instructions(&program);
    let cpi = generate_cpi(&program);
    let accounts = generate_accounts(&program);

    quote! {
        // TODO: remove once we allow segmented paths in `Accounts` structs.
        use #mod_name::*;

        #[cfg(not(feature = "no-entrypoint"))]
        anchor_lang::solana_program::entrypoint!(entry);
        #[cfg(not(feature = "no-entrypoint"))]
        fn entry(program_id: &Pubkey, accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
            if instruction_data.len() < 8 {
                return Err(ProgramError::Custom(99));
            }

            let mut instruction_data: &[u8] = instruction_data;
            let sighash: [u8; 8] = {
                let mut sighash: [u8; 8] = [0; 8];
                sighash.copy_from_slice(&instruction_data[..8]);
                instruction_data = &instruction_data[8..];
                sighash
            };

            if cfg!(not(feature = "no-idl")) {
                if sighash == anchor_lang::idl::IDL_IX_TAG.to_le_bytes() {
                    return __private::__idl(program_id, accounts, &instruction_data);
                }
            }

            #dispatch
        }

        // Create a private module to not clutter the program's namespace.
        mod __private {
            use super::*;

            #handlers_non_inlined
        }

        #accounts

        #instructions

        #methods

        #cpi
    }
}

pub fn generate_dispatch(program: &Program) -> proc_macro2::TokenStream {
    // Dispatch the state constructor.
    let ctor_state_dispatch_arm = match &program.state {
        None => quote! { /* no-op */ },
        Some(state) => match state.ctor_and_anchor.is_some() {
            false => quote! {},
            true => {
                let variant_arm = generate_ctor_variant(state);
                let ctor_args = generate_ctor_args(state);
                let ix_name: proc_macro2::TokenStream =
                    generate_ctor_variant_name().parse().unwrap();
                let sighash_arr = sighash_ctor();
                let sighash_tts: proc_macro2::TokenStream =
                    format!("{:?}", sighash_arr).parse().unwrap();
                quote! {
                    #sighash_tts => {
                        let ix = instruction::#ix_name::deserialize(&mut instruction_data)
                            .map_err(|_| ProgramError::Custom(1))?; // todo: error code
                        let instruction::#variant_arm = ix;
                        __private::__ctor(program_id, accounts, #(#ctor_args),*)
                    }
                }
            }
        },
    };

    // Dispatch the state impl instructions.
    let state_dispatch_arms: Vec<proc_macro2::TokenStream> = match &program.state {
        None => vec![],
        Some(s) => s
            .impl_block_and_methods
            .as_ref()
            .map(|(_impl_block, methods)| {
                methods
										.iter()
										.map(|rpc: &crate::StateRpc| {
												let rpc_arg_names: Vec<&syn::Ident> =
														rpc.args.iter().map(|arg| &arg.name).collect();
												let name = &rpc.raw_method.sig.ident.to_string();
												let rpc_name: proc_macro2::TokenStream = { format!("__{}", name).parse().unwrap() };
												let variant_arm =
														generate_ix_variant(rpc.raw_method.sig.ident.to_string(), &rpc.args, true);
												let ix_name = generate_ix_variant_name(rpc.raw_method.sig.ident.to_string(), true);
												let sighash_arr = sighash(SIGHASH_STATE_NAMESPACE, &name);
												let sighash_tts: proc_macro2::TokenStream =
														format!("{:?}", sighash_arr).parse().unwrap();
												quote! {
														#sighash_tts => {
																let ix = instruction::#ix_name::deserialize(&mut instruction_data)
																		.map_err(|_| ProgramError::Custom(1))?; // todo: error code
																let instruction::#variant_arm = ix;
																__private::#rpc_name(program_id, accounts, #(#rpc_arg_names),*)
														}
												}
										})
										.collect()
            })
            .unwrap_or(vec![]),
    };

    // Dispatch all trait interface implementations.
    let trait_dispatch_arms: Vec<proc_macro2::TokenStream> = match &program.state {
        None => vec![],
        Some(s) => s
            .interfaces
						.as_ref()
						.map(|interfaces| {
								interfaces
										.iter()
										.flat_map(|iface: &crate::StateInterface| {
												iface
														.methods
														.iter()
														.map(|m: &crate::StateRpc| {
																let rpc_arg_names: Vec<&syn::Ident> =
																		m.args.iter().map(|arg| &arg.name).collect();
																let name = &m.raw_method.sig.ident.to_string();
																let rpc_name: proc_macro2::TokenStream =  format!("__{}_{}", iface.trait_name, name).parse().unwrap();
																let raw_args: Vec<&syn::PatType> = m
																		.args
																		.iter()
																		.map(|arg: &crate::RpcArg| &arg.raw_arg)
																		.collect();
																let sighash_arr = sighash(&iface.trait_name, &m.ident.to_string());
																let sighash_tts: proc_macro2::TokenStream =
																		format!("{:?}", sighash_arr).parse().unwrap();
																let args_struct = {
																		if m.args.len() == 0 {
																				quote! {
																						#[derive(anchor_lang::AnchorSerialize, anchor_lang::AnchorDeserialize)]
																						struct Args;
																				}
																		} else {
																				quote! {
																						#[derive(anchor_lang::AnchorSerialize, anchor_lang::AnchorDeserialize)]
																						struct Args {
																								#(#raw_args),*
																						}
																				}
																		}
																};
																quote! {
																		#sighash_tts => {
																				#args_struct
																				let ix = Args::deserialize(&mut instruction_data)
																						.map_err(|_| ProgramError::Custom(1))?; // todo: error code
																				let Args {
																						#(#rpc_arg_names),*
																				} = ix;
																				__private::#rpc_name(program_id, accounts, #(#rpc_arg_names),*)
																		}
																}
														})
														.collect::<Vec<proc_macro2::TokenStream>>()
										})
										.collect()
						})
						.unwrap_or(vec![])
    };

    // Dispatch all global instructions.
    let dispatch_arms: Vec<proc_macro2::TokenStream> = program
        .rpcs
        .iter()
        .map(|rpc| {
            let rpc_arg_names: Vec<&syn::Ident> = rpc.args.iter().map(|arg| &arg.name).collect();
            let rpc_name = &rpc.raw_method.sig.ident;
            let ix_name = generate_ix_variant_name(rpc.raw_method.sig.ident.to_string(), false);
            let sighash_arr = sighash(SIGHASH_GLOBAL_NAMESPACE, &rpc_name.to_string());
            let sighash_tts: proc_macro2::TokenStream =
                format!("{:?}", sighash_arr).parse().unwrap();
            let variant_arm =
                generate_ix_variant(rpc.raw_method.sig.ident.to_string(), &rpc.args, false);
            quote! {
                #sighash_tts => {
                    let ix = instruction::#ix_name::deserialize(&mut instruction_data)
                        .map_err(|_| ProgramError::Custom(1))?; // todo: error code
                    let instruction::#variant_arm = ix;
                    __private::#rpc_name(program_id, accounts, #(#rpc_arg_names),*)
                }
            }
        })
        .collect();

    quote! {
        match sighash {
            #ctor_state_dispatch_arm
            #(#state_dispatch_arms)*
            #(#trait_dispatch_arms)*
            #(#dispatch_arms)*
            _ => {
                msg!("Fallback functions are not supported. If you have a use case, please file an issue.");
                Err(ProgramError::Custom(99))
            }
        }
    }
}

// Generate non-inlined wrappers for each instruction handler, since Solana's
// BPF max stack size can't handle reasonable sized dispatch trees without doing
// so.
pub fn generate_non_inlined_handlers(program: &Program) -> proc_macro2::TokenStream {
    let program_name = &program.name;
    let non_inlined_idl: proc_macro2::TokenStream = {
        quote! {
            // Entry for all IDL related instructions. Use the "no-idl" feature
            // to eliminate this code, for example, if one wants to make the
            // IDL no longer mutable or if one doesn't want to store the IDL
            // on chain.
            #[inline(never)]
            #[cfg(not(feature = "no-idl"))]
            pub fn __idl(program_id: &Pubkey, accounts: &[AccountInfo], idl_ix_data: &[u8]) -> ProgramResult {
                let mut accounts = accounts;
                let mut data: &[u8] = idl_ix_data;

                let ix = anchor_lang::idl::IdlInstruction::deserialize(&mut data)
                    .map_err(|_| ProgramError::Custom(2))?; // todo

                match ix {
                    anchor_lang::idl::IdlInstruction::Create { data_len } => {
                        let mut accounts = anchor_lang::idl::IdlCreateAccounts::try_accounts(program_id, &mut accounts)?;
                        __idl_create_account(program_id, &mut accounts, data_len)?;
                        accounts.exit(program_id)?;
                    },
                    anchor_lang::idl::IdlInstruction::Write { data } => {
                        let mut accounts = anchor_lang::idl::IdlAccounts::try_accounts(program_id, &mut accounts)?;
                        __idl_write(program_id, &mut accounts, data)?;
                        accounts.exit(program_id)?;
                    },
                    anchor_lang::idl::IdlInstruction::Clear => {
                        let mut accounts = anchor_lang::idl::IdlAccounts::try_accounts(program_id, &mut accounts)?;
                        __idl_clear(program_id, &mut accounts)?;
                        accounts.exit(program_id)?;
                    },
                    anchor_lang::idl::IdlInstruction::SetAuthority { new_authority } => {
                        let mut accounts = anchor_lang::idl::IdlAccounts::try_accounts(program_id, &mut accounts)?;
                        __idl_set_authority(program_id, &mut accounts, new_authority)?;
                        accounts.exit(program_id)?;
                    }
                }
                Ok(())
            }

            #[inline(never)]
            #[cfg(feature = "no-idl")]
            pub fn __idl(program_id: &Pubkey, accounts: &[AccountInfo], idl_ix_data: &[u8]) -> ProgramResult {
                Err(anchor_lang::solana_program::program_error::ProgramError::Custom(99))
            }

            // One time IDL account initializer. Will faill on subsequent
            // invocations.
            #[inline(never)]
            pub fn __idl_create_account(
                program_id: &Pubkey,
                accounts: &mut anchor_lang::idl::IdlCreateAccounts,
                data_len: u64,
            ) -> ProgramResult {
                // Create the IDL's account.
                let from = accounts.from.key;
                let (base, nonce) = Pubkey::find_program_address(&[], accounts.program.key);
                let seed = anchor_lang::idl::IdlAccount::seed();
                let owner = accounts.program.key;
                let to = Pubkey::create_with_seed(&base, seed, owner).unwrap();
                // Space: account discriminator || authority pubkey || vec len || vec data
                let space = 8 + 32 + 4 + data_len as usize;
                let lamports = accounts.rent.minimum_balance(space);
                let seeds = &[&[nonce][..]];
                let ix = anchor_lang::solana_program::system_instruction::create_account_with_seed(
                    from,
                    &to,
                    &base,
                    seed,
                    lamports,
                    space as u64,
                    owner,
                );
                anchor_lang::solana_program::program::invoke_signed(
                    &ix,
                    &[
                        accounts.from.clone(),
                        accounts.to.clone(),
                        accounts.base.clone(),
                        accounts.system_program.clone(),
                    ],
                    &[seeds],
                )?;

                // Deserialize the newly created account.
                let mut idl_account = {
                    let mut account_data =  accounts.to.try_borrow_data()?;
                    let mut account_data_slice: &[u8] = &account_data;
                    anchor_lang::idl::IdlAccount::try_deserialize_unchecked(
                        &mut account_data_slice,
                    )?
                };

                // Set the authority.
                idl_account.authority = *accounts.from.key;

                // Store the new account data.
                let mut data = accounts.to.try_borrow_mut_data()?;
                let dst: &mut [u8] = &mut data;
                let mut cursor = std::io::Cursor::new(dst);
                idl_account.try_serialize(&mut cursor)?;

                Ok(())
            }

            #[inline(never)]
            pub fn __idl_write(
                program_id: &Pubkey,
                accounts: &mut anchor_lang::idl::IdlAccounts,
                idl_data: Vec<u8>,
            ) -> ProgramResult {
                let mut idl = &mut accounts.idl;
                idl.data.extend(idl_data);
                Ok(())
            }

            #[inline(never)]
            pub fn __idl_clear(
                program_id: &Pubkey,
                accounts: &mut anchor_lang::idl::IdlAccounts,
            ) -> ProgramResult {
                accounts.idl.data = vec![];
                Ok(())
            }

            #[inline(never)]
            pub fn __idl_set_authority(
                program_id: &Pubkey,
                accounts: &mut anchor_lang::idl::IdlAccounts,
                new_authority: Pubkey,
            ) -> ProgramResult {
                accounts.idl.authority = new_authority;
                Ok(())
            }
        }
    };
    let non_inlined_ctor: proc_macro2::TokenStream = match &program.state {
        None => quote! {},
        Some(state) => match state.ctor_and_anchor.as_ref() {
            None => quote! {},
            Some((_ctor, anchor_ident)) => {
                let ctor_typed_args = generate_ctor_typed_args(state);
                let ctor_untyped_args = generate_ctor_args(state);
                let name = &state.strct.ident;
                let mod_name = &program.name;
                quote! {
                    // One time state account initializer. Will faill on subsequent
                    // invocations.
                    #[inline(never)]
                    pub fn __ctor(program_id: &Pubkey, accounts: &[AccountInfo], #(#ctor_typed_args),*) -> ProgramResult {
                        let mut remaining_accounts: &[AccountInfo] = accounts;

                        // Deserialize accounts.
                        let ctor_accounts = anchor_lang::Ctor::try_accounts(program_id, &mut remaining_accounts)?;
                        let mut ctor_user_def_accounts = #anchor_ident::try_accounts(program_id, &mut remaining_accounts)?;

                        // Invoke the ctor.
                        let instance = #mod_name::#name::new(
                            anchor_lang::Context::new(
                                program_id,
                                &mut ctor_user_def_accounts,
                                remaining_accounts,
                            ),
                            #(#ctor_untyped_args),*
                        )?;

                        // Create the solana account for the ctor data.
                        let from = ctor_accounts.from.key;
                        let (base, nonce) = Pubkey::find_program_address(&[], ctor_accounts.program.key);
                        let seed = anchor_lang::ProgramState::<#name>::seed();
                        let owner = ctor_accounts.program.key;
                        let to = Pubkey::create_with_seed(&base, seed, owner).unwrap();
                        // Add 8 for the account discriminator.
                        let space = 8 + instance.try_to_vec().map_err(|_| ProgramError::Custom(1))?.len();
                        let lamports = ctor_accounts.rent.minimum_balance(space);
                        let seeds = &[&[nonce][..]];
                        let ix = anchor_lang::solana_program::system_instruction::create_account_with_seed(
                            from,
                            &to,
                            &base,
                            seed,
                            lamports,
                            space as u64,
                            owner,
                        );
                        anchor_lang::solana_program::program::invoke_signed(
                            &ix,
                            &[
                                ctor_accounts.from.clone(),
                                ctor_accounts.to.clone(),
                                ctor_accounts.base.clone(),
                                ctor_accounts.system_program.clone(),
                            ],
                            &[seeds],
                        )?;

                        // Serialize the state and save it to storage.
                        ctor_user_def_accounts.exit(program_id)?;
                        let mut data = ctor_accounts.to.try_borrow_mut_data()?;
                        let dst: &mut [u8] = &mut data;
                        let mut cursor = std::io::Cursor::new(dst);
                        instance.try_serialize(&mut cursor)?;

                        Ok(())
                    }
                }
            }
        },
    };
    let non_inlined_state_handlers: Vec<proc_macro2::TokenStream> = match &program.state {
        None => vec![],
        Some(state) => state
            .impl_block_and_methods
            .as_ref()
            .map(|(_impl_block, methods)| {
                methods
										.iter()
										.map(|rpc| {
												let rpc_params: Vec<_> = rpc.args.iter().map(|arg| &arg.raw_arg).collect();
												let rpc_arg_names: Vec<&syn::Ident> =
														rpc.args.iter().map(|arg| &arg.name).collect();
												let private_rpc_name: proc_macro2::TokenStream = {
														let n = format!("__{}", &rpc.raw_method.sig.ident.to_string());
														n.parse().unwrap()
												};
												let rpc_name = &rpc.raw_method.sig.ident;
												let state_ty: proc_macro2::TokenStream = state.name.parse().unwrap();
												let anchor_ident = &rpc.anchor_ident;
												quote! {
														#[inline(never)]
														pub fn #private_rpc_name(
																program_id: &Pubkey,
																accounts: &[AccountInfo],
																#(#rpc_params),*
														) -> ProgramResult {

																let mut remaining_accounts: &[AccountInfo] = accounts;
																if remaining_accounts.len() == 0 {
																		return Err(ProgramError::Custom(1)); // todo
																}

																// Deserialize the program state account.
																let state_account = &remaining_accounts[0];
																let mut state: #state_ty = {
																		let data = state_account.try_borrow_data()?;
																		let mut sliced: &[u8] = &data;
																		anchor_lang::AccountDeserialize::try_deserialize(&mut sliced)?
																};

																remaining_accounts = &remaining_accounts[1..];

																// Deserialize the program's execution context.
																let mut accounts = #anchor_ident::try_accounts(
																		program_id,
																		&mut remaining_accounts,
																)?;
																let ctx = Context::new(program_id, &mut accounts, remaining_accounts);

																// Execute user defined function.
																state.#rpc_name(
																		ctx,
																		#(#rpc_arg_names),*
																)?;

																// Serialize the state and save it to storage.
																accounts.exit(program_id)?;
																let mut data = state_account.try_borrow_mut_data()?;
																let dst: &mut [u8] = &mut data;
																let mut cursor = std::io::Cursor::new(dst);
																state.try_serialize(&mut cursor)?;

																Ok(())
														}
												}
										})
										.collect()
            })
            .unwrap_or(vec![]),
    };
    let non_inlined_state_trait_handlers: Vec<proc_macro2::TokenStream> = match &program.state {
        None => Vec::new(),
        Some(state) => state
            .interfaces
            .as_ref()
            .map(|interfaces| {
                interfaces
                    .iter()
                    .flat_map(|iface: &crate::StateInterface| {
                        iface
														.methods
														.iter()
														.map(|rpc| {
																let rpc_params: Vec<_> = rpc.args.iter().map(|arg| &arg.raw_arg).collect();
																let rpc_arg_names: Vec<&syn::Ident> =
																		rpc.args.iter().map(|arg| &arg.name).collect();
																let private_rpc_name: proc_macro2::TokenStream = {
																		let n = format!("__{}_{}", iface.trait_name, &rpc.raw_method.sig.ident.to_string());
																		n.parse().unwrap()
																};
																let rpc_name = &rpc.raw_method.sig.ident;
																let state_ty: proc_macro2::TokenStream = state.name.parse().unwrap();
																let anchor_ident = &rpc.anchor_ident;

																if rpc.has_receiver {
																		quote! {
																				#[inline(never)]
																				pub fn #private_rpc_name(
																						program_id: &Pubkey,
																						accounts: &[AccountInfo],
																						#(#rpc_params),*
																				) -> ProgramResult {

																						let mut remaining_accounts: &[AccountInfo] = accounts;
																						if remaining_accounts.len() == 0 {
																								return Err(ProgramError::Custom(1)); // todo
																						}

																						// Deserialize the program state account.
																						let state_account = &remaining_accounts[0];
																						let mut state: #state_ty = {
																								let data = state_account.try_borrow_data()?;
																								let mut sliced: &[u8] = &data;
																								anchor_lang::AccountDeserialize::try_deserialize(&mut sliced)?
																						};

																						remaining_accounts = &remaining_accounts[1..];

																						// Deserialize the program's execution context.
																						let mut accounts = #anchor_ident::try_accounts(
																								program_id,
																								&mut remaining_accounts,
																						)?;
																						let ctx = Context::new(program_id, &mut accounts, remaining_accounts);

																						// Execute user defined function.
																						state.#rpc_name(
																								ctx,
																								#(#rpc_arg_names),*
																						)?;

																						// Serialize the state and save it to storage.
																						accounts.exit(program_id)?;
																						let mut data = state_account.try_borrow_mut_data()?;
																						let dst: &mut [u8] = &mut data;
																						let mut cursor = std::io::Cursor::new(dst);
																						state.try_serialize(&mut cursor)?;

																						Ok(())
																				}
																		}
																} else {
																		let state_name: proc_macro2::TokenStream = state.name.parse().unwrap();
																		quote! {
																				#[inline(never)]
																				pub fn #private_rpc_name(
																						program_id: &Pubkey,
																						accounts: &[AccountInfo],
																						#(#rpc_params),*
																				) -> ProgramResult {
																						let mut remaining_accounts: &[AccountInfo] = accounts;
																						let mut accounts = #anchor_ident::try_accounts(
																								program_id,
																								&mut remaining_accounts,
																						)?;
																						#state_name::#rpc_name(
																								Context::new(program_id, &mut accounts, remaining_accounts),
																								#(#rpc_arg_names),*
																						)?;
																						accounts.exit(program_id)
																				}
																		}
																}
														})
														.collect::<Vec<proc_macro2::TokenStream>>()
                    })
                    .collect()
            })
            .unwrap_or(Vec::new()),
    };
    let non_inlined_handlers: Vec<proc_macro2::TokenStream> = program
        .rpcs
        .iter()
        .map(|rpc| {
            let rpc_params: Vec<_> = rpc.args.iter().map(|arg| &arg.raw_arg).collect();
            let rpc_arg_names: Vec<&syn::Ident> = rpc.args.iter().map(|arg| &arg.name).collect();
            let rpc_name = &rpc.raw_method.sig.ident;
            let anchor = &rpc.anchor_ident;

            quote! {
                #[inline(never)]
                pub fn #rpc_name(
                    program_id: &Pubkey,
                    accounts: &[AccountInfo],
                    #(#rpc_params),*
                ) -> ProgramResult {
                    let mut remaining_accounts: &[AccountInfo] = accounts;
                    let mut accounts = #anchor::try_accounts(program_id, &mut remaining_accounts)?;
                    #program_name::#rpc_name(
                        Context::new(program_id, &mut accounts, remaining_accounts),
                        #(#rpc_arg_names),*
                    )?;
                    accounts.exit(program_id)
                }
            }
        })
        .collect();

    quote! {
        #non_inlined_idl
        #non_inlined_ctor
        #(#non_inlined_state_handlers)*
        #(#non_inlined_state_trait_handlers)*
        #(#non_inlined_handlers)*
    }
}

pub fn generate_ctor_variant(state: &State) -> proc_macro2::TokenStream {
    let ctor_args = generate_ctor_args(state);
    let ctor_variant_name: proc_macro2::TokenStream = generate_ctor_variant_name().parse().unwrap();
    if ctor_args.len() == 0 {
        quote! {
            #ctor_variant_name
        }
    } else {
        quote! {
            #ctor_variant_name {
                #(#ctor_args),*
            }
        }
    }
}

pub fn generate_ctor_variant_name() -> String {
    "__Ctor".to_string()
}

pub fn generate_ctor_typed_variant_with_semi(program: &Program) -> proc_macro2::TokenStream {
    match &program.state {
        None => quote! {},
        Some(state) => {
            let ctor_args: Vec<proc_macro2::TokenStream> = generate_ctor_typed_args(state)
                .iter()
                .map(|arg| {
                    format!("pub {}", parser::tts_to_string(&arg))
                        .parse()
                        .unwrap()
                })
                .collect();
            if ctor_args.len() == 0 {
                quote! {
                    #[derive(AnchorSerialize, AnchorDeserialize)]
                    pub struct __Ctor;
                }
            } else {
                quote! {
                    #[derive(AnchorSerialize, AnchorDeserialize)]
                    pub struct __Ctor {
                        #(#ctor_args),*
                    }
                }
            }
        }
    }
}

fn generate_ctor_typed_args(state: &State) -> Vec<syn::PatType> {
    state
        .ctor_and_anchor
        .as_ref()
        .map(|(ctor, _anchor_ident)| {
            ctor.sig
                .inputs
                .iter()
                .filter_map(|arg: &syn::FnArg| match arg {
                    syn::FnArg::Typed(pat_ty) => {
                        let mut arg_str = parser::tts_to_string(&pat_ty.ty);
                        arg_str.retain(|c| !c.is_whitespace());
                        if arg_str.starts_with("Context<") {
                            return None;
                        }
                        Some(pat_ty.clone())
                    }
                    _ => panic!("Invalid syntaxe,"),
                })
                .collect()
        })
        .unwrap_or(Vec::new())
}

fn generate_ctor_args(state: &State) -> Vec<Box<syn::Pat>> {
    state
        .ctor_and_anchor
        .as_ref()
        .map(|(ctor, _anchor_ident)| {
            ctor.sig
                .inputs
                .iter()
                .filter_map(|arg: &syn::FnArg| match arg {
                    syn::FnArg::Typed(pat_ty) => {
                        let mut arg_str = parser::tts_to_string(&pat_ty.ty);
                        arg_str.retain(|c| !c.is_whitespace());
                        if arg_str.starts_with("Context<") {
                            return None;
                        }
                        Some(pat_ty.pat.clone())
                    }
                    _ => panic!(""),
                })
                .collect()
        })
        .unwrap_or(Vec::new())
}

pub fn generate_ix_variant(
    name: String,
    args: &[RpcArg],
    underscore: bool,
) -> proc_macro2::TokenStream {
    let rpc_arg_names: Vec<&syn::Ident> = args.iter().map(|arg| &arg.name).collect();
    let rpc_name_camel: proc_macro2::TokenStream = {
        let n = name.to_camel_case();
        if underscore {
            format!("__{}", n).parse().unwrap()
        } else {
            n.parse().unwrap()
        }
    };

    if args.len() == 0 {
        quote! {
            #rpc_name_camel
        }
    } else {
        quote! {
            #rpc_name_camel {
                #(#rpc_arg_names),*
            }
        }
    }
}

pub fn generate_ix_variant_name(name: String, underscore: bool) -> proc_macro2::TokenStream {
    let n = name.to_camel_case();
    if underscore {
        format!("__{}", n).parse().unwrap()
    } else {
        n.parse().unwrap()
    }
}

pub fn generate_methods(program: &Program) -> proc_macro2::TokenStream {
    let program_mod = &program.program_mod;
    quote! {
        #program_mod
    }
}

pub fn generate_instructions(program: &Program) -> proc_macro2::TokenStream {
    let ctor_variant = generate_ctor_typed_variant_with_semi(program);
    let state_method_variants: Vec<proc_macro2::TokenStream> = match &program.state {
        None => vec![],
        Some(state) => state
            .impl_block_and_methods
            .as_ref()
            .map(|(_impl_block, methods)| {
                methods
										.iter()
										.map(|method| {
												let rpc_name_camel: proc_macro2::TokenStream = {
														let name = format!(
																"__{}",
																&method.raw_method.sig.ident.to_string().to_camel_case(),
														);
														name.parse().unwrap()
												};
												let raw_args: Vec<proc_macro2::TokenStream> = method
														.args
														.iter()
														.map(|arg| {
																format!("pub {}", parser::tts_to_string(&arg.raw_arg))
																		.parse()
																		.unwrap()
														})
														.collect();

												let ix_data_trait = {
														let name = method.raw_method.sig.ident.to_string();
														let sighash_arr = sighash(SIGHASH_GLOBAL_NAMESPACE, &name);
														let sighash_tts: proc_macro2::TokenStream =
																format!("{:?}", sighash_arr).parse().unwrap();
														quote! {
																impl anchor_lang::InstructionData for #rpc_name_camel {
																		fn data(&self) -> Vec<u8> {
																				let mut d = #sighash_tts.to_vec();
																				d.append(&mut self.try_to_vec().expect("Should always serialize"));
																				d
																		}
																}
														}
												};

												// If no args, output a "unit" variant instead of a struct variant.
												if method.args.len() == 0 {
														quote! {
																#[derive(AnchorSerialize, AnchorDeserialize)]
																pub struct #rpc_name_camel;

																#ix_data_trait
														}
												} else {
														quote! {
																#[derive(AnchorSerialize, AnchorDeserialize)]
																pub struct #rpc_name_camel {
																		#(#raw_args),*
																}

																#ix_data_trait
														}
												}
										})
										.collect()
            })
            .unwrap_or(Vec::new()),
    };
    let variants: Vec<proc_macro2::TokenStream> = program
        .rpcs
        .iter()
        .map(|rpc| {
            let name = &rpc.raw_method.sig.ident.to_string();
            let rpc_name_camel =
                proc_macro2::Ident::new(&name.to_camel_case(), rpc.raw_method.sig.ident.span());
            let raw_args: Vec<proc_macro2::TokenStream> = rpc
                .args
                .iter()
                .map(|arg| {
                    format!("pub {}", parser::tts_to_string(&arg.raw_arg))
                        .parse()
                        .unwrap()
                })
                .collect();
            let ix_data_trait = {
                let sighash_arr = sighash(SIGHASH_GLOBAL_NAMESPACE, &name);
                let sighash_tts: proc_macro2::TokenStream =
                    format!("{:?}", sighash_arr).parse().unwrap();
                quote! {
                    impl anchor_lang::InstructionData for #rpc_name_camel {
                        fn data(&self) -> Vec<u8> {
                            let mut d = #sighash_tts.to_vec();
                            d.append(&mut self.try_to_vec().expect("Should always serialize"));
                            d
                        }
                    }
                }
            };
            // If no args, output a "unit" variant instead of a struct variant.
            if rpc.args.len() == 0 {
                quote! {
                    #[derive(AnchorSerialize, AnchorDeserialize)]
                    pub struct #rpc_name_camel;

                    #ix_data_trait
                }
            } else {
                quote! {
                    #[derive(AnchorSerialize, AnchorDeserialize)]
                    pub struct #rpc_name_camel {
                        #(#raw_args),*
                    }

                    #ix_data_trait
                }
            }
        })
        .collect();

    quote! {
        /// `instruction` is a macro generated module containing the program's
        /// instruction enum, where each variant is created from each method
        /// handler in the `#[program]` mod. These should be used directly, when
        /// specifying instructions on a client.
        pub mod instruction {
            use super::*;

            #ctor_variant
            #(#state_method_variants)*
            #(#variants)*
        }
    }
}

fn generate_accounts(program: &Program) -> proc_macro2::TokenStream {
    let mut accounts = std::collections::HashSet::new();

    // Go through state accounts.
    if let Some(state) = &program.state {
        if let Some((_impl_block, methods)) = &state.impl_block_and_methods {
            for rpc in methods {
                let anchor_ident = &rpc.anchor_ident;
                // TODO: move to fn and share with accounts.rs.
                let macro_name = format!(
                    "__client_accounts_{}",
                    anchor_ident.to_string().to_snake_case()
                );
                accounts.insert(macro_name);
            }
        }
    }

    // Go through instruction accounts.
    for rpc in &program.rpcs {
        let anchor_ident = &rpc.anchor_ident;
        // TODO: move to fn and share with accounts.rs.
        let macro_name = format!(
            "__client_accounts_{}",
            anchor_ident.to_string().to_snake_case()
        );
        accounts.insert(macro_name);
    }

    // Build the tokens from all accounts
    let account_structs: Vec<proc_macro2::TokenStream> = accounts
        .iter()
        .map(|macro_name: &String| {
            let macro_name: proc_macro2::TokenStream = macro_name.parse().unwrap();
            quote! {
                pub use crate::#macro_name::*;
            }
        })
        .collect();

    // TODO: calculate the account size and add it as a constant field to
    //       each struct here. This is convenient for Rust clients.

    quote! {
        /// `accounts` is a macro generated module, providing a set of structs
        /// mirroring the structs deriving `Accounts`, where each field is
        /// a `Pubkey`. This is useful for specifying accounts for a client.
        pub mod accounts {
            #(#account_structs)*
        }
    }
}

fn generate_cpi(program: &Program) -> proc_macro2::TokenStream {
    let cpi_methods: Vec<proc_macro2::TokenStream> = program
        .rpcs
        .iter()
        .map(|rpc| {
            let accounts_ident = &rpc.anchor_ident;
            let cpi_method = {
                let ix_variant =
                    generate_ix_variant(rpc.raw_method.sig.ident.to_string(), &rpc.args, false);
                let method_name = &rpc.ident;
                let args: Vec<&syn::PatType> = rpc.args.iter().map(|arg| &arg.raw_arg).collect();
                let name = &rpc.raw_method.sig.ident.to_string();
                let sighash_arr = sighash(SIGHASH_GLOBAL_NAMESPACE, &name);
                let sighash_tts: proc_macro2::TokenStream =
                    format!("{:?}", sighash_arr).parse().unwrap();
                quote! {
                    pub fn #method_name<'a, 'b, 'c, 'info>(
                        ctx: CpiContext<'a, 'b, 'c, 'info, #accounts_ident<'info>>,
                        #(#args),*
                    ) -> ProgramResult {
                        let ix = {
                            let ix = instruction::#ix_variant;
                            let mut ix_data = AnchorSerialize::try_to_vec(&ix)
                                .map_err(|_| ProgramError::InvalidInstructionData)?;
                            let mut data = #sighash_tts.to_vec();
                            data.append(&mut ix_data);
                            let accounts = ctx.accounts.to_account_metas(None);
                            anchor_lang::solana_program::instruction::Instruction {
                                program_id: *ctx.program.key,
                                accounts,
                                data,
                            }
                        };
                        let mut acc_infos = ctx.accounts.to_account_infos();
                        acc_infos.push(ctx.program.clone());
                        anchor_lang::solana_program::program::invoke_signed(
                            &ix,
                            &acc_infos,
                            ctx.signer_seeds,
                        )
                    }
                }
            };

            cpi_method
        })
        .collect();
    quote! {
        #[cfg(feature = "cpi")]
        pub mod cpi {
            use super::*;

            #(#cpi_methods)*
        }
    }
}

// We don't technically use sighash, because the input arguments aren't given.
// Rust doesn't have method overloading so no need to use the arguments.
// However, we do namespace methods in the preeimage so that we can use
// different traits with the same method name.
pub fn sighash(namespace: &str, name: &str) -> [u8; 8] {
    let preimage = format!("{}::{}", namespace, name);

    let mut sighash = [0u8; 8];
    sighash.copy_from_slice(&crate::hash::hash(preimage.as_bytes()).to_bytes()[..8]);
    sighash
}

fn sighash_ctor() -> [u8; 8] {
    let namespace = SIGHASH_STATE_NAMESPACE;
    let preimage = format!("{}::new", namespace);

    let mut sighash = [0u8; 8];
    sighash.copy_from_slice(&crate::hash::hash(preimage.as_bytes()).to_bytes()[..8]);
    sighash
}
