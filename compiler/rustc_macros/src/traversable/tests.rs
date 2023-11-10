use super::{parse_quote, traversable_derive, visit, Foldable, ToTokens, Traversable};
use syn::visit_mut::VisitMut;

/// A folder that normalizes syn types for comparison in tests.
struct Normalizer;

/// Generates a folding method for [`Normalizer`] that ensures certain collections
/// are sorted consistently, thus eliminating any non-deterministic output.
macro_rules! normalizing_sort {
    ($($method:ident($field:ident in $ty:ty);)*) => {$(
        fn $method(&mut self, i: &mut $ty) {
            syn::visit_mut::$method(self, i);
            let mut vec = std::mem::take(&mut i.$field).into_iter().collect::<Vec<_>>();
            vec.sort_unstable_by_key(|x| x.to_token_stream().to_string());
            i.$field = vec.into_iter().collect();
        }
    )*};
}

impl VisitMut for Normalizer {
    // Each of the following fields in the following types can be reordered without
    // affecting semantics, and therefore need to be normalized.
    normalizing_sort! {
        visit_where_clause_mut(predicates in syn::WhereClause);
        visit_predicate_lifetime_mut(bounds in syn::PredicateLifetime);
        visit_bound_lifetimes_mut(lifetimes in syn::BoundLifetimes);
        visit_lifetime_param_mut(bounds in syn::LifetimeParam);
        visit_type_param_mut(bounds in syn::TypeParam);
        visit_type_impl_trait_mut(bounds in syn::TypeImplTrait);
        visit_type_trait_object_mut(bounds in syn::TypeTraitObject);
        visit_generics_mut(params in syn::Generics);
    }

    // For convenience, we also simplify paths by removing absolute crate/module
    // references.
    fn visit_path_mut(&mut self, i: &mut syn::Path) {
        syn::visit_mut::visit_path_mut(self, i);

        let n = if i.leading_colon.is_some() && i.segments.len() >= 2 {
            let segment = &i.segments[0];
            if *segment == parse_quote! { rustc_middle } {
                if i.segments.len() >= 3 && i.segments[1] == parse_quote! { ty } {
                    let segment = &i.segments[2];
                    if *segment == parse_quote! { fold } || *segment == parse_quote! { visit } {
                        3
                    } else {
                        2
                    }
                } else {
                    1
                }
            } else if *segment == parse_quote! { core } {
                let segment = &i.segments[1];
                if *segment == parse_quote! { ops } {
                    2
                } else if *segment == parse_quote! { result } {
                    i.segments.len() - 1
                } else {
                    return;
                }
            } else {
                return;
            }
        } else {
            return;
        };

        *i = syn::Path {
            leading_colon: None,
            segments: std::mem::take(&mut i.segments).into_iter().skip(n).collect(),
        };
    }
}

#[derive(Default, Debug)]
struct Errors(Vec<String>);

impl Errors {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn contains(&self, message: &str) -> bool {
        self.0.iter().any(|error| error.starts_with(message))
    }
}

impl<E: ToString> From<E> for Errors {
    fn from(err: E) -> Self {
        Self(vec![err.to_string()])
    }
}

impl visit::Visit<'_> for Errors {
    fn visit_macro(&mut self, i: &syn::Macro) {
        if i.path == parse_quote! { ::core::compile_error } {
            self.0.push(
                i.parse_body::<syn::LitStr>()
                    .expect("expected compile_error macro to be invoked with a string literal")
                    .value(),
            );
        } else {
            syn::visit::visit_macro(self, i)
        }
    }
}

fn result<T: Traversable>(input: syn::DeriveInput) -> Result<syn::ItemImpl, Errors> {
    traversable_derive::<T>(synstructure::Structure::new(&input))
        .and_then(syn::parse2)
        .map_err(Into::into)
        .and_then(|result| {
            let mut errors = Errors::default();
            visit::Visit::visit_item_const(&mut errors, &result);
            errors
                .is_empty()
                .then(|| {
                    let syn::Expr::Block(syn::ExprBlock {
                        block: syn::Block { stmts, .. }, ..
                    }) = *result.expr
                    else {
                        panic!("expected const expr to be a block")
                    };
                    assert_eq!(stmts.len(), 1, "expected const expr to contain a single statement");
                    let syn::Stmt::Item(syn::Item::Impl(mut item_impl)) =
                        stmts.into_iter().next().unwrap()
                    else {
                        panic!("expected statement in const expr to be an impl")
                    };

                    Normalizer.visit_item_impl_mut(&mut item_impl);
                    item_impl
                })
                .ok_or(errors)
        })
}

fn expect_success<T: Traversable>(input: syn::DeriveInput, expected: syn::ItemImpl) {
    let result = result::<T>(input);
    assert!(
        result.as_ref().is_ok_and(|actual| *actual == expected),
        "EXPECTED: {:?}\nACTUAL:   {:?}",
        Ok::<_, Errors>(expected.into_token_stream().to_string()),
        result.map(|success| success.into_token_stream().to_string()),
    );
}

fn expect_failure<T: Traversable>(input: syn::DeriveInput, expected: &str) {
    let result = result::<T>(input);
    assert!(
        result.as_ref().is_err_and(|errors| errors.contains(expected)),
        "EXPECTED: Err(\"{expected}...\")\nACTUAL:   {:?}",
        result.map(|success| success.into_token_stream().to_string()),
    );
}

macro_rules! expect {
    ({$($input:tt)*} => {$($output:tt)*} $($rest:tt)*) => {
        expect_success::<Foldable>(parse_quote! { $($input)* }, parse_quote! { $($output)* });
        expect! { $($rest)* }
    };
    ({$($input:tt)*} => $msg:literal $($rest:tt)*) => {
        expect_failure::<Foldable>(parse_quote! { $($input)* }, $msg);
        expect! { $($rest)* }
    };
    () => {};
}

#[test]
fn only_potentially_non_trivial_fields_are_constrained_and_folded() {
    expect! {
        {
            struct SomethingInteresting<'a, 'b, 'c, 'tcx: 'b, T>(
                T,
                T::Assoc,
                Const<'tcx>,
                Complex<'tcx, T>,
                Generic<T>,
                Trivial,
                TrivialGeneric<'a, Foo>,
                NotTrivial<'b>,
                NotTrivial<'c>,
            ) where 'tcx: 'c;
        } => {
            impl<'a, 'b, 'c, 'tcx: 'b, T> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<'a, 'b, 'c, 'tcx, T>
            where
                'tcx: 'c,
                Complex<'tcx, T>: TypeFoldable<TyCtxt<'tcx>>,
                Generic<T>: TypeFoldable<TyCtxt<'tcx>>,
                Self: TypeVisitable<TyCtxt<'tcx>>,
                T: TypeFoldable<TyCtxt<'tcx>>,
                T::Assoc: TypeFoldable<TyCtxt<'tcx>>
                // the following constraints are NOT required, because the fields are not generic:
                //     Const<'tcx>: TypeFoldable<TyCtxt<'tcx>>
                //     Trivial: TypeFoldable<TyCtxt<'tcx>>
                //     TrivialGeneric<'a, Foo>: TypeFoldable<TyCtxt<'tcx>>
                //     NotTrivial<'b>: TypeFoldable<TyCtxt<'tcx>>
                //     NotTrivial<'c>: TypeFoldable<TyCtxt<'tcx>>
            {
                fn try_fold_with<_T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut _T) -> Result<Self, _T::Error> {
                    Ok(match self {
                        SomethingInteresting (
                            __binding_0,
                            __binding_1,
                            __binding_2,
                            __binding_3,
                            __binding_4,
                            __binding_5,
                            __binding_6,
                            __binding_7,
                            __binding_8,
                        ) => { SomethingInteresting(
                            TypeFoldable::try_fold_with(__binding_0, folder)?,
                            TypeFoldable::try_fold_with(__binding_1, folder)?,
                            TypeFoldable::try_fold_with(__binding_2, folder)?,
                            TypeFoldable::try_fold_with(__binding_3, folder)?,
                            TypeFoldable::try_fold_with(__binding_4, folder)?,
                            __binding_5, // not folded
                            __binding_6, // not folded
                            TypeFoldable::try_fold_with(__binding_7, folder)?,
                            TypeFoldable::try_fold_with(__binding_8, folder)?,
                        )}
                    })
                }
            }
        }
    }
}

#[test]
fn skipping_trivial_type_requires_justification() {
    expect! {
        {
            struct NothingInteresting<'a>;
        } => "Traversal of guaranteed trivial types are no-ops by default"

        {
            #[skip_traversal()]
            struct NothingInteresting<'a>;
        } => "Traversal of guaranteed trivial types are no-ops by default"

        {
            #[skip_traversal(but_impl_despite_trivial_because = ".")]
            struct NothingInteresting<'a>;
        } => {
            impl<'a, 'tcx> TypeFoldable<TyCtxt<'tcx>> for NothingInteresting<'a> {
                fn try_fold_with<T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut T) -> Result<Self, T::Error> {
                    Ok(self) // no attempt to fold
                }
            }
        }
    }
}

#[test]
fn skipping_potentially_non_trivial_type_requires_justification() {
    expect! {
        {
            #[skip_traversal()]
            struct SomethingInteresting<'tcx>;
        } => "Justification must be provided for skipping potentially non-trivial types"

        {
            #[skip_traversal(but_impl_despite_trivial_because = ".")]
            struct SomethingInteresting<'tcx>;
        } => "`but_impl_despite_trivial_because` is only valid on guaranteed trivial types"

        {
            #[skip_traversal(because_trivial)]
            struct SomethingInteresting<'tcx>;
        } => "`because_trivial` is only valid on potentially non-trivial variants or fields"

        {
            #[skip_traversal(despite_potential_miscompilation_because = ".")]
            struct SomethingInteresting<'tcx>;
        } => {
            impl<'tcx> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<'tcx> {
                fn try_fold_with<T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut T) -> Result<Self, T::Error> {
                    Ok(self) // no attempt to fold fields
                }
            }
        }
    }
}

#[test]
fn skipping_potentially_non_trivial_field_requires_justification() {
    expect! {
        {
            struct SomethingInteresting<'tcx>(
                #[skip_traversal()]
                Const<'tcx>,
            );
        } => "Justification must be provided for skipping potentially non-trivial fields"

        {
            struct SomethingInteresting<'tcx>(
                #[skip_traversal(because_trivial)]
                Const<'tcx>,
            );
        } => {
            impl<'tcx> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<'tcx>
            where
                Const<'tcx>: TriviallyTraversable // `because_trivial`
            {
                fn try_fold_with<T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut T) -> Result<Self, T::Error> {
                    Ok(match self {
                        SomethingInteresting(__binding_0,) => { SomethingInteresting(__binding_0,) } // not folded
                    })
                }
            }
        }

        {
            struct SomethingInteresting<'tcx>(
                #[skip_traversal(despite_potential_miscompilation_because = ".")]
                Const<'tcx>,
            );
        } => {
            impl<'tcx> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<'tcx>
            // no `Const<'tcx>: TriviallyTraversable` constraint
            {
                fn try_fold_with<T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut T) -> Result<Self, T::Error> {
                    Ok(match self {
                        SomethingInteresting(__binding_0,) => { SomethingInteresting(__binding_0,) } // not folded
                    })
                }
            }
        }
    }
}

#[test]
fn skipping_generic_type_requires_justification() {
    expect! {
        {
            #[skip_traversal()]
            struct SomethingInteresting<T>;
        } => "Justification must be provided for skipping potentially non-trivial types"

        {
            #[skip_traversal(despite_potential_miscompilation_because = ".")]
            struct SomethingInteresting<T>;
        } => {
            impl<'tcx, T> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<T>
            where
                Self: TypeVisitable<TyCtxt<'tcx>>
            {
                fn try_fold_with<_T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut _T) -> Result<Self, _T::Error> {
                    Ok(self) // no attempt to fold fields
                }
            }
        }
    }
}

#[test]
fn skipping_generic_field_requires_justification() {
    expect! {
        {
            struct SomethingInteresting<T>(
                #[skip_traversal()]
                T,
            );
        } => "Justification must be provided for skipping potentially non-trivial fields"

        {
            struct SomethingInteresting<T>(
                #[skip_traversal(because_trivial)]
                T,
            );
        } => {
            impl<'tcx, T> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<T>
            where
                Self: TypeVisitable<TyCtxt<'tcx>>,
                T: TriviallyTraversable // `because_trivial`
            {
                fn try_fold_with<_T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut _T) -> Result<Self, _T::Error> {
                    Ok(match self {
                        SomethingInteresting(__binding_0,) => { SomethingInteresting(__binding_0,) } // not folded
                    })
                }
            }
        }

        {
            struct SomethingInteresting<T>(
                #[skip_traversal(despite_potential_miscompilation_because = ".")]
                T,
            );
        } => {
            impl<'tcx, T> TypeFoldable<TyCtxt<'tcx>> for SomethingInteresting<T>
            where
                Self: TypeVisitable<TyCtxt<'tcx>>
                // no `T: TriviallyTraversable` constraint
            {
                fn try_fold_with<_T: FallibleTypeFolder<TyCtxt<'tcx>>>(self, folder: &mut _T) -> Result<Self, _T::Error> {
                    Ok(match self {
                        SomethingInteresting(__binding_0,) => { SomethingInteresting(__binding_0,) } // not folded
                    })
                }
            }
        }

        {
            struct SomethingInteresting<T>(
                #[skip_traversal(because_trivial)]
                T,
                T,
            );
        } => "This annotation only makes sense if all fields of type `T` are annotated identically"

        {
            struct SomethingInteresting<T>(
                #[skip_traversal(despite_potential_miscompilation_because = ".")]
                T,
                #[skip_traversal(because_trivial)]
                T,
            );
        } => "This annotation only makes sense if all fields of type `T` are annotated identically"
    }
}
