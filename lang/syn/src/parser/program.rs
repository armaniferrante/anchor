use crate::parser;
use crate::{Program, Rpc, RpcArg, State, StateInterface, StateRpc};

pub fn parse(program_mod: syn::ItemMod) -> Program {
    let mod_ident = &program_mod.ident;

    let mod_content = &program_mod.content.as_ref().unwrap().1;

    // Parse the state struct singleton.
    let state: Option<State> = {
        let strct: Option<&syn::ItemStruct> = mod_content
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item_strct) => {
                    let attrs = &item_strct.attrs;
                    if attrs.is_empty() {
                        return None;
                    }
                    let attr_label = attrs[0].path.get_ident().map(|i| i.to_string());
                    if attr_label != Some("state".to_string()) {
                        return None;
                    }

                    Some(item_strct)
                }
                _ => None,
            })
            .next();

        let impl_block: Option<syn::ItemImpl> = match strct {
            None => None,
            Some(strct) => mod_content
                .iter()
                .filter_map(|item| match item {
                    syn::Item::Impl(item_impl) => {
                        let impl_ty_str = parser::tts_to_string(&item_impl.self_ty);
                        let strct_name = strct.ident.to_string();
                        if item_impl.trait_.is_some() {
                            return None;
                        }
                        if strct_name != impl_ty_str {
                            return None;
                        }
                        Some(item_impl.clone())
                    }
                    _ => None,
                })
                .next(),
        };

        // All program interface implementations.
        let trait_impls: Option<Vec<StateInterface>> = strct.map(|_strct| {
            mod_content
                .iter()
                .filter_map(|item| match item {
                    syn::Item::Impl(item_impl) => {
                        let trait_name = match &item_impl.trait_ {
                            None => return None,
                            Some((_, path, _)) => path
                                .segments
                                .iter()
                                .next()
                                .expect("Must have one segmeent in a path")
                                .ident
                                .clone()
                                .to_string(),
                        };
                        if item_impl.trait_.is_none() {
                            return None;
                        }
                        let methods = parse_state_trait_methods(item_impl);
                        Some(StateInterface {
                            trait_name,
                            methods,
                        })
                    }
                    _ => None,
                })
                .collect::<Vec<StateInterface>>()
        });

        strct.map(|strct| {
            // Chop off the `#[state]` attribute. It's just a marker.
            let mut strct = strct.clone();
            strct.attrs = vec![];

            let ctor_and_anchor = match &impl_block {
                None => None,
                Some(impl_block) => {
                    impl_block
                        .items
                        .iter()
                        .filter_map(|item: &syn::ImplItem| match item {
                            syn::ImplItem::Method(m) => {
                                if m.sig.ident.to_string() == "new" {
                                    let ctx_arg = m.sig.inputs.first().unwrap(); // todo: unwrap.
                                    match ctx_arg {
                                        syn::FnArg::Receiver(_) => panic!("invalid syntax"),
                                        syn::FnArg::Typed(arg) => {
                                            Some((m.clone(), extract_ident(&arg).clone()))
                                        }
                                    }
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        })
                        .next()
                        .clone()
                }
            };

            let impl_block_and_methods = impl_block.map(|impl_block| {
                let methods: Vec<StateRpc> = impl_block
                    .items
                    .iter()
                    .filter_map(|item: &syn::ImplItem| match item {
                        syn::ImplItem::Method(m) => match m.sig.inputs.first() {
                            None => None,
                            Some(arg) => match arg {
                                syn::FnArg::Typed(_) => None,
                                syn::FnArg::Receiver(_) => {
                                    let mut args = m
                                        .sig
                                        .inputs
                                        .iter()
                                        .filter_map(|arg| match arg {
                                            syn::FnArg::Receiver(_) => None,
                                            syn::FnArg::Typed(arg) => Some(arg),
                                        })
                                        .map(|raw_arg| {
                                            let ident = match &*raw_arg.pat {
                                                syn::Pat::Ident(ident) => &ident.ident,
                                                _ => panic!("invalid syntax"),
                                            };
                                            RpcArg {
                                                name: ident.clone(),
                                                raw_arg: raw_arg.clone(),
                                            }
                                        })
                                        .collect::<Vec<RpcArg>>();
                                    // Remove the Anchor accounts argument
                                    let anchor = args.remove(0);
                                    let anchor_ident = extract_ident(&anchor.raw_arg).clone();

                                    Some(StateRpc {
                                        raw_method: m.clone(),
                                        ident: m.sig.ident.clone(),
                                        args,
                                        anchor_ident,
                                        has_receiver: true,
                                    })
                                }
                            },
                        },
                        _ => None,
                    })
                    .collect();
                (impl_block.clone(), methods)
            });
            State {
                name: strct.ident.to_string(),
                strct: strct.clone(),
                interfaces: trait_impls,
                impl_block_and_methods,
                ctor_and_anchor,
            }
        })
    };

    let methods: Vec<&syn::ItemFn> = mod_content
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(item_fn) => Some(item_fn),
            _ => None,
        })
        .collect();

    let rpcs: Vec<Rpc> = methods
        .clone()
        .into_iter()
        .map(|method: &syn::ItemFn| {
            let mut args: Vec<RpcArg> = method
                .sig
                .inputs
                .iter()
                .map(|arg: &syn::FnArg| match arg {
                    syn::FnArg::Typed(arg) => {
                        let ident = match &*arg.pat {
                            syn::Pat::Ident(ident) => &ident.ident,
                            _ => panic!("invalid syntax"),
                        };
                        RpcArg {
                            name: ident.clone(),
                            raw_arg: arg.clone(),
                        }
                    }
                    _ => panic!("invalid syntax"),
                })
                .collect();
            // Remove the Anchor accounts argument
            let anchor = args.remove(0);
            let anchor_ident = extract_ident(&anchor.raw_arg).clone();

            Rpc {
                raw_method: method.clone(),
                ident: method.sig.ident.clone(),
                args,
                anchor_ident,
            }
        })
        .collect();

    Program {
        state,
        rpcs,
        name: mod_ident.clone(),
        program_mod,
    }
}

fn extract_ident(path_ty: &syn::PatType) -> &proc_macro2::Ident {
    let p = match &*path_ty.ty {
        syn::Type::Path(p) => &p.path,
        _ => panic!("invalid syntax"),
    };
    let segment = p.segments.first().unwrap();
    let generic_args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(args) => args,
        _ => panic!("invalid syntax"),
    };
    let generic_ty = generic_args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
        .next()
        .unwrap();
    let path = match generic_ty {
        syn::Type::Path(ty_path) => &ty_path.path,
        _ => panic!("invalid syntax"),
    };
    &path.segments[0].ident
}

fn parse_state_trait_methods(item_impl: &syn::ItemImpl) -> Vec<StateRpc> {
    item_impl
        .items
        .iter()
        .filter_map(|item: &syn::ImplItem| match item {
            syn::ImplItem::Method(m) => match m.sig.inputs.first() {
                None => None,
                Some(_arg) => {
                    let mut has_receiver = false;
                    let mut args = m
                        .sig
                        .inputs
                        .iter()
                        .filter_map(|arg| match arg {
                            syn::FnArg::Receiver(_) => {
                                has_receiver = true;
                                None
                            }
                            syn::FnArg::Typed(arg) => Some(arg),
                        })
                        .map(|raw_arg| {
                            let ident = match &*raw_arg.pat {
                                syn::Pat::Ident(ident) => &ident.ident,
                                _ => panic!("invalid syntax"),
                            };
                            RpcArg {
                                name: ident.clone(),
                                raw_arg: raw_arg.clone(),
                            }
                        })
                        .collect::<Vec<RpcArg>>();
                    // Remove the Anchor accounts argument
                    let anchor = args.remove(0);
                    let anchor_ident = extract_ident(&anchor.raw_arg).clone();

                    Some(StateRpc {
                        raw_method: m.clone(),
                        ident: m.sig.ident.clone(),
                        args,
                        anchor_ident,
                        has_receiver,
                    })
                }
            },
            _ => None,
        })
        .collect()
}
