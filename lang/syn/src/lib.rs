//! DSL syntax tokens.

#[cfg(feature = "idl")]
use crate::idl::{IdlAccount, IdlAccountItem, IdlAccounts};
use anyhow::Result;
#[cfg(feature = "idl")]
use heck::MixedCase;
use quote::quote;
use std::collections::HashMap;

pub mod codegen;
#[cfg(feature = "hash")]
pub mod hash;
#[cfg(not(feature = "hash"))]
pub(crate) mod hash;
#[cfg(feature = "idl")]
pub mod idl;
pub mod parser;

#[derive(Debug)]
pub struct Program {
    pub state: Option<State>,
    pub rpcs: Vec<Rpc>,
    pub name: syn::Ident,
    pub program_mod: syn::ItemMod,
}

// State struct singleton.
#[derive(Debug)]
pub struct State {
    pub name: String,
    pub strct: syn::ItemStruct,
    pub ctor_and_anchor: Option<(syn::ImplItemMethod, syn::Ident)>,
    pub impl_block_and_methods: Option<(syn::ItemImpl, Vec<StateRpc>)>,
    pub interfaces: Option<Vec<StateInterface>>,
}

#[derive(Debug)]
pub struct StateRpc {
    pub raw_method: syn::ImplItemMethod,
    pub ident: syn::Ident,
    pub args: Vec<RpcArg>,
    pub anchor_ident: syn::Ident,
    // True if there exists a &self on the method.
    pub has_receiver: bool,
}

#[derive(Debug)]
pub struct StateInterface {
    pub trait_name: String,
    pub methods: Vec<StateRpc>,
}

#[derive(Debug)]
pub struct Rpc {
    pub raw_method: syn::ItemFn,
    pub ident: syn::Ident,
    pub args: Vec<RpcArg>,
    // The ident for the struct deriving Accounts.
    pub anchor_ident: syn::Ident,
}

#[derive(Debug)]
pub struct RpcArg {
    pub name: proc_macro2::Ident,
    pub raw_arg: syn::PatType,
}

#[derive(Debug)]
pub struct AccountsStruct {
    // Name of the accounts struct.
    pub ident: syn::Ident,
    // Generics + lifetimes on the accounts struct.
    pub generics: syn::Generics,
    // Fields on the accounts struct.
    pub fields: Vec<AccountField>,
}

impl AccountsStruct {
    pub fn new(strct: syn::ItemStruct, fields: Vec<AccountField>) -> Self {
        let ident = strct.ident.clone();
        let generics = strct.generics.clone();
        Self {
            ident,
            generics,
            fields,
        }
    }

    // Returns all program owned accounts in the Accounts struct.
    //
    // `global_accs` is given to "link" account types that are embedded
    // in each other.
    pub fn account_tys(
        &self,
        global_accs: &HashMap<String, AccountsStruct>,
    ) -> Result<Vec<String>> {
        let mut tys = vec![];
        for f in &self.fields {
            match f {
                AccountField::Field(f) => {
                    if let Ty::ProgramAccount(pty) = &f.ty {
                        tys.push(pty.account_ident.to_string());
                    }
                }
                AccountField::AccountsStruct(comp_f) => {
                    let accs = global_accs.get(&comp_f.symbol).ok_or(anyhow::format_err!(
                        "Invalid account type: {}",
                        comp_f.symbol
                    ))?;
                    tys.extend(accs.account_tys(global_accs)?);
                }
            }
        }
        Ok(tys)
    }

    #[cfg(feature = "idl")]
    pub fn idl_accounts(
        &self,
        global_accs: &HashMap<String, AccountsStruct>,
    ) -> Vec<IdlAccountItem> {
        self.fields
            .iter()
            .map(|acc: &AccountField| match acc {
                AccountField::AccountsStruct(comp_f) => {
                    let accs_strct = global_accs
                        .get(&comp_f.symbol)
                        .expect("Could not reslve Accounts symbol");
                    let accounts = accs_strct.idl_accounts(global_accs);
                    IdlAccountItem::IdlAccounts(IdlAccounts {
                        name: comp_f.ident.to_string().to_mixed_case(),
                        accounts,
                    })
                }
                AccountField::Field(acc) => IdlAccountItem::IdlAccount(IdlAccount {
                    name: acc.ident.to_string().to_mixed_case(),
                    is_mut: acc.is_mut,
                    is_signer: acc.is_signer,
                }),
            })
            .collect::<Vec<_>>()
    }
}

#[derive(Debug)]
pub enum AccountField {
    // Use a `String` instead of the `AccountsStruct` because all
    // accounts structs aren't visible to a single derive macro.
    //
    // When we need the global context, we fill in the String with the
    // appropriate values. See, `account_tys` as an example.
    AccountsStruct(CompositeField), // Composite
    Field(Field),                   // Primitive
}

#[derive(Debug)]
pub struct CompositeField {
    pub ident: syn::Ident,
    pub symbol: String,
    pub constraints: Vec<Constraint>,
    pub raw_field: syn::Field,
}

// An account in the accounts struct.
#[derive(Debug)]
pub struct Field {
    pub ident: syn::Ident,
    pub ty: Ty,
    pub constraints: Vec<Constraint>,
    pub is_mut: bool,
    pub is_signer: bool,
    pub is_init: bool,
}

impl Field {
    pub fn typed_ident(&self) -> proc_macro2::TokenStream {
        let name = &self.ident;

        let ty = match &self.ty {
            Ty::AccountInfo => quote! { AccountInfo },
            Ty::ProgramState(ty) => {
                let account = &ty.account_ident;
                quote! {
                    ProgramState<#account>
                }
            }
            Ty::ProgramAccount(ty) => {
                let account = &ty.account_ident;
                quote! {
                    ProgramAccount<#account>
                }
            }
            Ty::CpiAccount(ty) => {
                let account = &ty.account_ident;
                quote! {
                    CpiAccount<#account>
                }
            }
            Ty::Sysvar(ty) => {
                let account = match ty {
                    SysvarTy::Clock => quote! {Clock},
                    SysvarTy::Rent => quote! {Rent},
                    SysvarTy::EpochSchedule => quote! {EpochSchedule},
                    SysvarTy::Fees => quote! {Fees},
                    SysvarTy::RecentBlockHashes => quote! {RecentBlockHashes},
                    SysvarTy::SlotHashes => quote! {SlotHashes},
                    SysvarTy::SlotHistory => quote! {SlotHistory},
                    SysvarTy::StakeHistory => quote! {StakeHistory},
                    SysvarTy::Instructions => quote! {Instructions},
                    SysvarTy::Rewards => quote! {Rewards},
                };
                quote! {
                    Sysvar<#account>
                }
            }
        };

        quote! {
            #name: #ty
        }
    }
}

// A type of an account field.
#[derive(Debug, PartialEq)]
pub enum Ty {
    AccountInfo,
    ProgramState(ProgramStateTy),
    ProgramAccount(ProgramAccountTy),
    CpiAccount(CpiAccountTy),
    Sysvar(SysvarTy),
}

#[derive(Debug, PartialEq)]
pub enum SysvarTy {
    Clock,
    Rent,
    EpochSchedule,
    Fees,
    RecentBlockHashes,
    SlotHashes,
    SlotHistory,
    StakeHistory,
    Instructions,
    Rewards,
}

#[derive(Debug, PartialEq)]
pub struct ProgramStateTy {
    pub account_ident: syn::Ident,
}

#[derive(Debug, PartialEq)]
pub struct ProgramAccountTy {
    // The struct type of the account.
    pub account_ident: syn::Ident,
}

#[derive(Debug, PartialEq)]
pub struct CpiAccountTy {
    // The struct type of the account.
    pub account_ident: syn::Ident,
}

// An access control constraint for an account.
#[derive(Debug)]
pub enum Constraint {
    Signer(ConstraintSigner),
    BelongsTo(ConstraintBelongsTo),
    Literal(ConstraintLiteral),
    Owner(ConstraintOwner),
    RentExempt(ConstraintRentExempt),
    Seeds(ConstraintSeeds),
}

#[derive(Debug)]
pub struct ConstraintBelongsTo {
    pub join_target: proc_macro2::Ident,
}

#[derive(Debug)]
pub struct ConstraintSigner {}

#[derive(Debug)]
pub struct ConstraintLiteral {
    pub tokens: proc_macro2::TokenStream,
}

#[derive(Debug)]
pub enum ConstraintOwner {
    Program,
    Skip,
}

#[derive(Debug)]
pub enum ConstraintRentExempt {
    Enforce,
    Skip,
}

#[derive(Debug)]
pub struct ConstraintSeeds {
    pub seeds: proc_macro2::Group,
}

#[derive(Debug)]
pub struct Error {
    pub name: String,
    pub raw_enum: syn::ItemEnum,
    pub ident: syn::Ident,
    pub codes: Vec<ErrorCode>,
}

#[derive(Debug)]
pub struct ErrorCode {
    pub id: u32,
    pub ident: syn::Ident,
    pub msg: Option<String>,
}
