mod parse;

use std::hash::Hash;

use devise::ext::{PathExt, TypeExt as _};
use devise::{Diagnostic, FromMeta, Result, SpanWrapped, Spanned};
use proc_macro2::{Span, TokenStream};
use syn::punctuated::Punctuated;
use syn::token::Comma;
use syn::GenericParam;

use crate::attribute::param::Guard;
use crate::http;
use crate::http_codegen::{Method, Optional};
use crate::proc_macro_ext::StringLit;
use crate::syn_ext::{IdentExt, TypeExt as _};

use self::parse::{Attribute, MethodAttribute, Route};

impl Route {
    pub fn guards(&self) -> impl Iterator<Item = &Guard> {
        self.param_guards()
            .chain(self.query_guards())
            .chain(self.data_guard.iter())
            .chain(self.request_guards.iter())
    }

    pub fn param_guards(&self) -> impl Iterator<Item = &Guard> {
        self.path_params.iter().filter_map(|p| p.guard())
    }

    pub fn query_guards(&self) -> impl Iterator<Item = &Guard> {
        self.query_params.iter().filter_map(|p| p.guard())
    }
}

fn query_decls(route: &Route) -> Option<TokenStream> {
    use devise::ext::{Split2, Split6};

    if route.query_params.is_empty() && route.query_guards().next().is_none() {
        return None;
    }

    define_spanned_export!(Span::call_site() =>
        __req, __data, _log, _form, Outcome, _Ok, _Err, _Some, _None
    );

    // Record all of the static parameters for later filtering.
    let (raw_name, raw_value) = route
        .query_params
        .iter()
        .filter_map(|s| s.r#static())
        .map(|name| match name.find('=') {
            Some(i) => (&name[..i], &name[i + 1..]),
            None => (name.as_str(), ""),
        })
        .split2();

    // Now record all of the dynamic parameters.
    let (name, matcher, ident, init_expr, push_expr, finalize_expr) = route
        .query_guards()
        .map(|guard| {
            let (name, ty) = (&guard.name, &guard.ty);
            let ident = guard.fn_ident.rocketized().with_span(ty.span());
            let matcher = match guard.trailing {
                true => quote_spanned!(name.span() => _),
                _ => quote!(#name),
            };

            define_spanned_export!(ty.span() => FromForm, _form);

            let ty = quote_spanned!(ty.span() => <#ty as #FromForm>);
            let init = quote_spanned!(ty.span() => #ty::init(#_form::Options::Lenient));
            let finalize = quote_spanned!(ty.span() => #ty::finalize(#ident));
            let push = match guard.trailing {
                true => quote_spanned!(ty.span() => #ty::push_value(&mut #ident, _f)),
                _ => quote_spanned!(ty.span() => #ty::push_value(&mut #ident, _f.shift())),
            };

            (name, matcher, ident, init, push, finalize)
        })
        .split6();

    #[allow(non_snake_case)]
    Some(quote! {
        let (#(#ident),*) = {
            let mut __e = #_form::Errors::new();
            #(let mut #ident = #init_expr;)*

            for _f in #__req.query_fields() {
                let _raw = (_f.name.source().as_str(), _f.value);
                let _key = _f.name.key_lossy().as_str();
                match (_raw, _key) {
                    // Skip static parameters so <param..> doesn't see them.
                    #(((#raw_name, #raw_value), _) => { /* skip */ },)*
                    #((_, #matcher) => #push_expr,)*
                    _ => { /* in case we have no trailing, ignore all else */ },
                }
            }

            #(
                let #ident = match #finalize_expr {
                    #_Ok(_v) => #_Some(_v),
                    #_Err(_err) => {
                        __e.extend(_err.with_name(#_form::NameView::new(#name)));
                        #_None
                    },
                };
            )*

            if !__e.is_empty() {
                #_log::warn_!("Query string failed to match route declaration.");
                for _err in __e { #_log::warn_!("{}", _err); }
                return #Outcome::Forward(#__data);
            }

            (#(#ident.unwrap()),*)
        };
    })
}

fn request_guard_decl(guard: &Guard) -> TokenStream {
    let (ident, ty) = (guard.fn_ident.rocketized(), &guard.ty);
    define_spanned_export!(ty.span() =>
        __req, __data, _request, _log, FromRequest, Outcome
    );

    quote_spanned! { ty.span() =>
        let #ident: #ty = match <#ty as #FromRequest>::from_request(#__req).await {
            #Outcome::Success(__v) => __v,
            #Outcome::Forward(_) => {
                #_log::warn_!("Request guard `{}` is forwarding.", stringify!(#ty));
                return #Outcome::Forward(#__data);
            },
            #Outcome::Failure((__c, __e)) => {
                #_log::warn_!("Request guard `{}` failed: {:?}.", stringify!(#ty), __e);
                return #Outcome::Failure(__c);
            }
        };
    }
}

fn param_guard_decl(guard: &Guard) -> TokenStream {
    let (i, name, ty) = (guard.index, &guard.name, &guard.ty);
    define_spanned_export!(ty.span() =>
        __req, __data, _log, _None, _Some, _Ok, _Err,
        Outcome, FromSegments, FromParam
    );

    // Returned when a dynamic parameter fails to parse.
    let parse_error = quote!({
        #_log::warn_!("Parameter guard `{}: {}` is forwarding: {:?}.",
            #name, stringify!(#ty), __error);

        #Outcome::Forward(#__data)
    });

    // All dynamic parameters should be found if this function is being called;
    // that's the point of statically checking the URI parameters.
    let expr = match guard.trailing {
        false => quote_spanned! { ty.span() =>
            match #__req.routed_segment(#i) {
                #_Some(__s) => match <#ty as #FromParam>::from_param(__s) {
                    #_Ok(__v) => __v,
                    #_Err(__error) => return #parse_error,
                },
                #_None => {
                    #_log::error_!("Internal invariant broken: dyn param not found.");
                    #_log::error_!("Please report this to the Rocket issue tracker.");
                    #_log::error_!("https://github.com/SergioBenitez/Rocket/issues");
                    return #Outcome::Forward(#__data);
                }
            }
        },
        true => quote_spanned! { ty.span() =>
            match <#ty as #FromSegments>::from_segments(#__req.routed_segments(#i..)) {
                #_Ok(__v) => __v,
                #_Err(__error) => return #parse_error,
            }
        },
    };

    let ident = guard.fn_ident.rocketized();
    quote!(let #ident: #ty = #expr;)
}

fn data_guard_decl(guard: &Guard) -> TokenStream {
    let (ident, ty) = (guard.fn_ident.rocketized(), &guard.ty);
    define_spanned_export!(ty.span() => _log, __req, __data, FromData, Outcome);

    quote_spanned! { ty.span() =>
        let #ident: #ty = match <#ty as #FromData>::from_data(#__req, #__data).await {
            #Outcome::Success(__d) => __d,
            #Outcome::Forward(__d) => {
                #_log::warn_!("Data guard `{}` is forwarding.", stringify!(#ty));
                return #Outcome::Forward(__d);
            }
            #Outcome::Failure((__c, __e)) => {
                #_log::warn_!("Data guard `{}` failed: {:?}.", stringify!(#ty), __e);
                return #Outcome::Failure(__c);
            }
        };
    }
}

fn internal_uri_macro_decl(route: &Route) -> TokenStream {
    // FIXME: Is this the right order? Does order matter?
    let uri_args = route
        .param_guards()
        .chain(route.query_guards())
        .map(|guard| (&guard.fn_ident, &guard.ty))
        .map(|(ident, ty)| quote!(#ident: #ty));

    // Generate a unique macro name based on the route's metadata.
    let macro_name = route.handler.sig.ident.prepend(crate::URI_MACRO_PREFIX);
    let inner_macro_name = macro_name.uniqueify_with(|mut hasher| {
        route.handler.sig.ident.hash(&mut hasher);
        route.attr.uri.path().hash(&mut hasher);
        route.attr.uri.query().hash(&mut hasher)
    });

    let route_uri = route.attr.uri.to_string();

    quote_spanned! { Span::call_site() =>
        #[doc(hidden)]
        #[macro_export]
        /// Rocket generated URI macro.
        macro_rules! #inner_macro_name {
            ($($token:tt)*) => {{
                rocket::rocket_internal_uri!(#route_uri, (#(#uri_args),*), $($token)*)
            }};
        }

        #[doc(hidden)]
        pub use #inner_macro_name as #macro_name;
    }
}

fn responder_outcome_expr(route: &Route) -> TokenStream {
    let ret_span = match route.handler.sig.output {
        syn::ReturnType::Default => route.handler.sig.ident.span(),
        syn::ReturnType::Type(_, ref ty) => ty.span(),
    };

    let user_handler_fn_name = if route.handler.sig.generics.params.is_empty() {
        let ident = &route.handler.sig.ident;
        quote!(#ident)
    } else {
        let ident = &route.handler.sig.ident;
        let generics = route
            .handler
            .sig
            .generics
            .params
            .clone()
            .into_iter()
            .filter_map(|p| match p {
                GenericParam::Type(syn::TypeParam { ident, .. }) => Some(ident),
                _ => None,
            })
            .collect::<Punctuated<_, Comma>>();
        quote!(#ident :: <#generics>)
    };
    let parameter_names = route
        .arguments
        .map
        .values()
        .map(|(ident, _)| ident.rocketized());

    let _await = route
        .handler
        .sig
        .asyncness
        .map(|a| quote_spanned!(a.span() => .await));

    define_spanned_export!(ret_span => __req, _route);
    quote_spanned! { ret_span =>
        let ___responder = #user_handler_fn_name(#(#parameter_names),*) #_await;
        #_route::Outcome::from(#__req, ___responder)
    }
}

fn sentinels_expr(route: &Route) -> TokenStream {
    let ret_ty = match route.handler.sig.output {
        syn::ReturnType::Default => None,
        syn::ReturnType::Type(_, ref ty) => Some(ty.with_stripped_lifetimes()),
    };

    let generic_idents: Vec<_> = route
        .handler
        .sig
        .generics
        .type_params()
        .map(|p| &p.ident)
        .collect();

    // Note: for a given route, we need to emit a valid graph of eligble
    // sentinels. This means that we don't have broken links, where a child
    // points to a parent that doesn't exist. The concern is that the
    // `is_concrete()` filter will cause a break in the graph.
    //
    // Here's a proof by cases for why this can't happen:
    //    1. if `is_concrete()` returns `false` for a (valid) type, it returns
    //       false for all of its parents. we consider this an axiom; this is
    //       the point of `is_concrete()`. the type is filtered out, so the
    //       theorem vacously holds
    //    2. if `is_concrete()` returns `true`, for a type `T`, it either:
    //      * returns `false` for the parent. by 1) it will return false for
    //        _all_ parents of the type, so no node in the graph can consider,
    //        directly or indirectly, `T` to be a child, and thus there are no
    //        broken links; the thereom holds
    //      * returns `true` for the parent, and so the type has a parent, and
    //      the theorem holds.
    //    3. these are all the cases. QED.

    const TY_MACS: &[&str] = &["ReaderStream", "TextStream", "ByteStream", "EventStream"];

    fn ty_mac_mapper(tokens: &TokenStream) -> Option<syn::Type> {
        use crate::bang::typed_stream::Input;

        match syn::parse2(tokens.clone()).ok()? {
            Input::Type(ty, ..) => Some(ty),
            Input::Tokens(..) => None,
        }
    }

    let eligible_types = route
        .guards()
        .map(|guard| &guard.ty)
        .chain(ret_ty.as_ref().into_iter())
        .flat_map(|ty| ty.unfold_with_ty_macros(TY_MACS, ty_mac_mapper))
        .filter(|ty| ty.is_concrete(&generic_idents))
        .map(|child| (child.parent, child.ty));

    let sentinel = eligible_types.map(|(parent, ty)| {
        define_spanned_export!(ty.span() => _sentinel);

        match parent {
            Some(p) if p.is_concrete(&generic_idents) => {
                quote_spanned!(ty.span() => #_sentinel::resolve!(#ty, #p))
            }
            Some(_) | None => quote_spanned!(ty.span() => #_sentinel::resolve!(#ty)),
        }
    });

    quote!(::std::vec![#(#sentinel),*])
}

fn codegen_route(route: Route, generic_trampoline_real_name: Option<syn::Ident>) -> Result<TokenStream> {
    use crate::exports::*;

    // Generate the declarations for all of the guards.
    let request_guards = route.request_guards.iter().map(request_guard_decl);
    let param_guards = route.param_guards().map(param_guard_decl);
    let query_guards = query_decls(&route);
    let data_guard = route.data_guard.as_ref().map(data_guard_decl);

    // Extract the sentinels from the route.
    let sentinels = sentinels_expr(&route);

    // Gather info about the function.
    let (vis, handler_fn) = (&route.handler.vis, &route.handler);
    let (handler_fn_name, static_info_name, impl_generics, bare_generic_idents, phantoms, phantom_values) =
        if handler_fn.sig.generics.params.is_empty() {
            let ident = handler_fn.sig.ident.clone();
            let static_info_name = quote!(String::from(::std::any::type_name::<#ident>()));
            (ident, static_info_name, None, None, Default::default(), Default::default())
        } else {
            let ident = handler_fn.sig.ident.clone();
            let generics = handler_fn.sig.generics.clone();
            let generic_idents = generics
                .params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Type(syn::TypeParam { ident, .. }) => Some(ident.clone()),
                    _ => None,
                })
                .collect::<Punctuated<_, Comma>>();

            let phantoms = generic_idents
                .iter()
                .map(|i| {
                    let phantom_ident =
                        syn::Ident::new(&format!("phantom_{}", i.to_string()), i.span());
                    let phantom_type = i.clone();
                    quote!(#phantom_ident : ::std::marker::PhantomData<#phantom_type>)
                })
                .collect::<Punctuated<_, Comma>>();
            let phantom_values = generic_idents
                .iter()
                .map(|i| {
                    let phantom_ident =
                        syn::Ident::new(&format!("phantom_{}", i.to_string()), i.span());
                    quote!(#phantom_ident : ::std::marker::PhantomData)
                })
                .collect::<Punctuated<_, Comma>>();
            let generic_trampoline_real_name = generic_trampoline_real_name.unwrap_or(ident.clone());
            let first_generic_ident = generic_idents.first().cloned().unwrap_or(syn::parse_str("Any").unwrap());
            let generic_trampoline_real_name_str = generic_trampoline_real_name.to_string();
            let gen_static_info_name = quote!(
                format!("{}:{}", ::std::any::type_name::< #first_generic_ident >(), #generic_trampoline_real_name_str)
            );
            (
                ident,
                gen_static_info_name,
                Some(generics),
                Some(quote!(#generic_idents)),
                phantoms,
                phantom_values,
            )
        };
    let generic_idents = bare_generic_idents.clone().map(|gi| quote!(< #gi >));
    let internal_uri_macro = internal_uri_macro_decl(&route);
    let responder_outcome = responder_outcome_expr(&route);

    let method = route.attr.method;
    let uri = route.attr.uri.to_string();
    let rank = Optional(route.attr.rank);
    let format = Optional(route.attr.format.as_ref());

    let monomorphized_function_generics = [quote!('__r)]
        .into_iter()
        .chain(
            impl_generics
                .clone()
                .map(|syn::Generics { params, .. }| quote!(#params)),
        )
        .collect::<Punctuated<_, Comma>>();
    let monomorphized_function_handler_generics = generic_idents.clone().map(|i| quote!(:: #i));

    Ok(quote! {
        #handler_fn

        #[doc(hidden)]
        #[allow(non_camel_case_types)]
        #[allow(non_snake_case)]
        /// Rocket code generated proxy structure.
        #vis struct #handler_fn_name #generic_idents { #phantoms }

        #[doc(hidden)]
        impl #impl_generics ::std::default::Default for #handler_fn_name #generic_idents {
            fn default() -> Self {
                Self {
                    #phantom_values
                }
            }
        }

        /// Rocket code generated proxy static conversion implementations.
        impl #impl_generics #handler_fn_name #generic_idents {
            #[allow(non_snake_case, unreachable_patterns, unreachable_code)]
            fn into_info(self) -> #_route::StaticInfo {
                fn monomorphized_function < #monomorphized_function_generics > (
                    #__req: &'__r #Request<'_>,
                    #__data: #Data<'__r>
                ) -> #_route::BoxFuture<'__r> {
                    #_Box::pin(async move {
                        #(#request_guards)*
                        #(#param_guards)*
                        #query_guards
                        #data_guard

                        #responder_outcome
                    })
                }

                #_route::StaticInfo {
                    name: #static_info_name,
                    method: #method,
                    uri: #uri,
                    handler: monomorphized_function #monomorphized_function_handler_generics,
                    format: #format,
                    rank: #rank,
                    sentinels: #sentinels,
                }
            }

            #[doc(hidden)]
            pub fn into_route(self) -> #Route {
                self.into_info().into()
            }
        }

        /// Rocket code generated wrapping URI macro.
        #internal_uri_macro
    })
}

fn complete_route(args: TokenStream, input: TokenStream) -> Result<TokenStream> {
    let function: syn::ItemFn = syn::parse2(input)
        .map_err(Diagnostic::from)
        .map_err(|diag| diag.help("`#[route]` can only be used on functions"))?;

    let attr_tokens = quote!(route(#args));
    let attribute = Attribute::from_meta(&syn::parse2(attr_tokens)?)?;
    codegen_route(Route::from(attribute, function)?, None)
}

fn incomplete_route(
    method: crate::http::Method,
    args: TokenStream,
    input: TokenStream,
) -> Result<TokenStream> {
    let method_str = method.to_string().to_lowercase();
    // FIXME(proc_macro): there should be a way to get this `Span`.
    let method_span = StringLit::new(format!("#[{}]", method), Span::call_site())
        .subspan(2..2 + method_str.len());

    let method_ident = syn::Ident::new(&method_str, method_span);

    let function: syn::ItemFn = syn::parse2(input)
        .map_err(Diagnostic::from)
        .map_err(|d| d.help(format!("#[{}] can only be used on functions", method_str)))?;

    let full_attr = quote!(#method_ident(#args));
    let method_attribute = MethodAttribute::from_meta(&syn::parse2(full_attr)?)?;

    let attribute = Attribute {
        method: SpanWrapped {
            full_span: method_span,
            key_span: None,
            span: method_span,
            value: Method(method),
        },
        uri: method_attribute.uri,
        data: method_attribute.data,
        format: method_attribute.format,
        rank: method_attribute.rank,
    };

    codegen_route(Route::from(attribute, function)?, None)
}

pub fn route_attribute<M: Into<Option<crate::http::Method>>>(
    method: M,
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> TokenStream {
    let result = match method.into() {
        Some(method) => incomplete_route(method, args.into(), input.into()),
        None => complete_route(args.into(), input.into()),
    };

    result.unwrap_or_else(|diag| diag.emit_as_item_tokens())
}

pub fn trait_attribute(args: proc_macro::TokenStream, input: proc_macro::TokenStream) -> TokenStream {
    let _ = syn::parse2::<syn::parse::Nothing>(args.into()).unwrap();
    let input = syn::parse2::<syn::ItemTrait>(input.into()).unwrap();

    let vis = input.vis;
    let trait_name = input.ident;
    let mut supertraits = input.supertraits;
    supertraits.push(syn::TypeParamBound::Trait(syn::TraitBound {
        paren_token: None,
        modifier: syn::TraitBoundModifier::None,
        lifetimes: None,
        path: syn::parse_str("::std::any::Any").unwrap(),
    }));
    supertraits.push(syn::TypeParamBound::Trait(syn::TraitBound {
        paren_token: None,
        modifier: syn::TraitBoundModifier::None,
        lifetimes: None,
        path: syn::parse_str("::std::marker::Sized").unwrap(),
    }));
    supertraits.push(syn::TypeParamBound::Lifetime(syn::Lifetime::new("'static", Span::call_site())));

    let normalize_route_attr = |a: &syn::Attribute| {
        static METHODS: [(&str, http::Method); 7] = [
            ("get", http::Method::Get),
            ("put", http::Method::Put),
            ("post", http::Method::Post),
            ("delete", http::Method::Delete),
            ("head", http::Method::Head),
            ("patch", http::Method::Patch),
            ("options", http::Method::Options),
        ];
        let is_method_attr = |seg| a.path.is_local(&[seg])
            || a.path.is_global(&["rocket", seg])
            || a.path.is_local(&["rocket", seg]);
        let find_method_attr = ||
            METHODS.iter()
                .filter_map(|(s, m)| if is_method_attr(s) { Some(m.clone()) } else { None })
                .next();

        let args = &a.tokens;
        syn::parse2(quote!(route #args)).ok().and_then(|route_meta|
            Attribute::from_meta(&route_meta).ok()
                .or_else(||
                    find_method_attr().and_then(|m| {
                        let as_ident = syn::Ident::new(&m.to_string().to_lowercase(), Span::call_site());
                        syn::parse2(quote!(#as_ident #args)).ok().and_then(|method_attr_meta| {
                            MethodAttribute::from_meta(&method_attr_meta).ok().map(|ma| {
                                Attribute {
                                    method: SpanWrapped {
                                        span: Span::call_site(),
                                        key_span: None,
                                        full_span: Span::call_site(),
                                        value: Method(m)
                                    },
                                    uri: ma.uri,
                                    data: ma.data,
                                    format: ma.format,
                                    rank: ma.rank,
                                }
                            })
                        })
                    })
                )
        )
    };

    let route_impl_generic = syn::Ident::new(&format!("TImpl{}", trait_name), trait_name.span());
    let mut route_impl_items = vec![];
    let filtered_trait_items = input
        .items
        .clone()
        .into_iter()
        .map(|mut ti| {
            if let syn::TraitItem::Method(ref mut tim) = ti {
                route_impl_items.push(tim.clone());
                let filtered_attrs = tim
                    .attrs
                    .clone()
                    .into_iter()
                    .filter_map(|a| if normalize_route_attr(&a).is_none() { Some(a) } else { None })
                    .collect();
                tim.attrs = filtered_attrs;
            }

            ti
        })
        .collect::<Vec<_>>();

    let push_sig_generic = |sig: &mut syn::Signature| {
        let type_param = GenericParam::Type(syn::TypeParam {
            attrs: vec![],
            ident: route_impl_generic.clone(),
            colon_token: Some(Default::default()),
            bounds: vec![syn::TypeParamBound::Trait(syn::TraitBound {
                paren_token: None,
                modifier: syn::TraitBoundModifier::None,
                lifetimes: None,
                path: trait_name.clone().into(),
            })]
                .into_iter()
                .collect(),
            eq_token: None,
            default: None,
        });
        sig.generics.params.push(type_param);
    };

    let trampoline_struct_name = syn::Ident::new(
        &format!("{}Trampoline", trait_name),
        trait_name.span().into(),
    );

    let mut trampoline_idents = vec![];

    let trampoline_items = route_impl_items
        .into_iter()
        .map(|syn::TraitItemMethod { attrs, mut sig, .. }| {
            use std::ops::Deref;
            push_sig_generic(&mut sig);
            let original_path = sig.ident.clone();
            let trampoline = syn::Ident::new(&format!("trampoline_{}", original_path), original_path.span().into());
            sig.ident = trampoline.clone();
            let args = sig
                .inputs
                .iter()
                .map(|arg| match arg {
                    syn::FnArg::Receiver(_) => {
                        panic!("Rocket trait routes with receiver arguments are invalid!")
                    }
                    syn::FnArg::Typed(syn::PatType { pat, .. }) => match pat.deref() {
                        syn::Pat::Ident(syn::PatIdent { ident, .. }) => syn::Expr::Path(syn::ExprPath {
                            attrs: vec![],
                            qself: None,
                            path: ident.clone().into(),
                        }),
                        x => panic!("Unsupported arg {:#?}", x),
                    },
                })
                .collect::<Vec<_>>();
            let stmt = quote!(
                return <#route_impl_generic as #trait_name>::#original_path(#(#args),*);
            );
            let stmts = vec![syn::parse2(stmt).unwrap()];
            let block = Box::new(syn::Block {
                brace_token: Default::default(),
                stmts,
            });

            let mut kept_attrs = vec![];
            let mut codegen_attrs = vec![];

            for attr in attrs {
                match normalize_route_attr(&attr) {
                    Some(ra) => codegen_attrs.push(ra),
                    None => kept_attrs.push(attr),
                }
            }

            trampoline_idents.push(quote!(#trampoline::<#route_impl_generic>));

            let fn_item = syn::ItemFn {
                attrs: kept_attrs,
                sig,
                block,
                vis: syn::Visibility::Inherited,
            };


            codegen_attrs.into_iter()
                .map(|ra| codegen_route(Route::from(ra, fn_item.clone()).unwrap(), Some(original_path.clone())).unwrap())
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<_>>();

    let res = quote!(
        #vis trait #trait_name: #supertraits {
            #(#filtered_trait_items)*

            fn routes() -> ::std::vec::Vec<::rocket::Route> {
                #trampoline_struct_name(::std::marker::PhantomData::<Self>).into()
            }
        }
        struct #trampoline_struct_name<T: #trait_name>(::std::marker::PhantomData<T>);
        const _: () = {
            #(#trampoline_items)*

            impl<#route_impl_generic: #trait_name> From<#trampoline_struct_name<#route_impl_generic>> for ::std::vec::Vec<::rocket::Route> {
                fn from(_: #trampoline_struct_name<#route_impl_generic>) -> Self {
                    ::rocket::routes![#(#trampoline_idents),*]
                }
            }

            ()
        };
    );
    res.into()
}