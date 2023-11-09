use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use smallvec::SmallVec;
use std::collections::{HashSet, VecDeque};
use syn::{
    parse_quote,
    visit::{self, Visit},
    Field, Generics, Lifetime,
};

use Type::*;

#[cfg(test)]
mod tests;

/// Generate a type parameter with the given `suffix` that does not conflict with
/// any of the `existing` generics.
fn gen_param(suffix: impl ToString, existing: &Generics) -> Ident {
    let mut suffix = suffix.to_string();
    while existing.type_params().any(|t| t.ident == suffix) {
        suffix.insert(0, '_');
    }
    Ident::new(&suffix, Span::call_site())
}

#[derive(Clone, Copy, PartialEq)]
enum Type {
    /// Describes a type that is not parameterised by the interner, and therefore cannot
    /// be of any interest to traversers.
    Trivial,

    /// Describes a type that is parameterised by an internable lifetime (`'tcx`, or any
    /// other lifetime parameter bounded thereby) but that is otherwise not generic.
    Internable,

    /// Describes a type that is generic.
    Generic,
}

pub struct Interner<'a> {
    /// Valid lifetimes of the `TyCtxt`; the first is always the `'tcx` lifetime,
    /// and the remainder are others that are bounded by it. If empty, the derive
    /// input was not parameterised by `'tcx` and the `TyCtxt` in the generated
    /// implementation should use a `'tcx` parameter that is unrelated to the input.
    lifetimes: SmallVec<[&'a Lifetime; 1]>,
}

impl<'a> Interner<'a> {
    /// Return the interner for an input with the given `generics`.
    fn resolve(generics: &'a Generics) -> Self {
        let mut lifetimes = SmallVec::new();
        let tcx = parse_quote! { 'tcx };

        let mut queue = VecDeque::from([&tcx]);
        while let Some(bound) = queue.pop_front() {
            if !lifetimes.contains(&bound) {
                for def in generics.lifetimes() {
                    if def.lifetime == *bound {
                        lifetimes.push(&def.lifetime);
                        queue.extend(&def.bounds);
                        if let Some(where_clause) = &generics.where_clause {
                            for pred in &where_clause.predicates {
                                if let syn::WherePredicate::Lifetime(syn::PredicateLifetime {
                                    lifetime,
                                    bounds,
                                    ..
                                }) = pred && lifetime == bound {
                                    queue.extend(bounds);
                                }
                            }
                        }
                    }
                }
            }
        }

        Self { lifetimes }
    }

    /// We consider a type to be internable if it references either a generic type parameter
    /// or an internable lifetime.
    fn type_of<'b>(
        &self,
        referenced_ty_params: &[&Ident],
        fields: impl IntoIterator<Item = &'b Field>,
    ) -> Type {
        struct Info<'a> {
            internable_lifetimes: &'a [&'a Lifetime],
            can_reference_interner: bool,
        }

        impl Visit<'_> for Info<'_> {
            fn visit_lifetime(&mut self, i: &Lifetime) {
                if self.internable_lifetimes.contains(&i) {
                    self.can_reference_interner = true;
                } else {
                    visit::visit_lifetime(self, i)
                }
            }
        }

        if !referenced_ty_params.is_empty() {
            Generic
        } else if !self.lifetimes.is_empty()
            && fields.into_iter().any(|field| {
                let mut info =
                    Info { internable_lifetimes: &self.lifetimes, can_reference_interner: false };
                info.visit_type(&field.ty);
                info.can_reference_interner
            })
        {
            Internable
        } else {
            Trivial
        }
    }
}

impl ToTokens for Interner<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let default = &parse_quote! { 'tcx };
        let lt = self.lifetimes.first().unwrap_or(&default);
        tokens.extend(quote! { ::rustc_middle::ty::TyCtxt<#lt> });
    }
}

pub struct Foldable;
pub struct Visitable;

/// An abstraction over traversable traits.
pub trait Traversable {
    /// The trait that this `Traversable` represents, parameterised by `interner`.
    fn traversable(interner: &Interner<'_>) -> TokenStream;

    /// Any supertraits that this trait is required to implement.
    fn supertraits(interner: &Interner<'_>) -> TokenStream;

    /// A (`noop`) traversal of this trait upon the `bind` expression.
    fn traverse(bind: TokenStream, noop: bool) -> TokenStream;

    /// A `match` arm for `variant`, where `f` generates the tokens for each binding.
    fn arm(
        variant: &synstructure::VariantInfo<'_>,
        f: impl FnMut(&synstructure::BindingInfo<'_>) -> TokenStream,
    ) -> TokenStream;

    /// The body of an implementation given the `interner`, `traverser` and match expression `body`.
    fn impl_body(
        interner: Interner<'_>,
        traverser: impl ToTokens,
        body: impl ToTokens,
    ) -> TokenStream;
}

impl Traversable for Foldable {
    fn traversable(interner: &Interner<'_>) -> TokenStream {
        quote! { ::rustc_middle::ty::fold::TypeFoldable<#interner> }
    }
    fn supertraits(interner: &Interner<'_>) -> TokenStream {
        Visitable::traversable(interner)
    }
    fn traverse(bind: TokenStream, noop: bool) -> TokenStream {
        if noop {
            bind
        } else {
            quote! { ::rustc_middle::ty::fold::TypeFoldable::try_fold_with(#bind, folder)? }
        }
    }
    fn arm(
        variant: &synstructure::VariantInfo<'_>,
        mut f: impl FnMut(&synstructure::BindingInfo<'_>) -> TokenStream,
    ) -> TokenStream {
        let bindings = variant.bindings();
        variant.construct(|_, index| f(&bindings[index]))
    }
    fn impl_body(
        interner: Interner<'_>,
        traverser: impl ToTokens,
        body: impl ToTokens,
    ) -> TokenStream {
        quote! {
            fn try_fold_with<#traverser: ::rustc_middle::ty::fold::FallibleTypeFolder<#interner>>(
                self,
                folder: &mut #traverser
            ) -> ::core::result::Result<Self, #traverser::Error> {
                ::core::result::Result::Ok(#body)
            }
        }
    }
}

impl Traversable for Visitable {
    fn traversable(interner: &Interner<'_>) -> TokenStream {
        quote! { ::rustc_middle::ty::visit::TypeVisitable<#interner> }
    }
    fn supertraits(_: &Interner<'_>) -> TokenStream {
        quote! { ::core::clone::Clone + ::core::fmt::Debug }
    }
    fn traverse(bind: TokenStream, noop: bool) -> TokenStream {
        if noop {
            quote! {}
        } else {
            quote! { ::rustc_middle::ty::visit::TypeVisitable::visit_with(#bind, visitor)?; }
        }
    }
    fn arm(
        variant: &synstructure::VariantInfo<'_>,
        f: impl FnMut(&synstructure::BindingInfo<'_>) -> TokenStream,
    ) -> TokenStream {
        variant.bindings().iter().map(f).collect()
    }
    fn impl_body(
        interner: Interner<'_>,
        traverser: impl ToTokens,
        body: impl ToTokens,
    ) -> TokenStream {
        quote! {
            fn visit_with<#traverser: ::rustc_middle::ty::visit::TypeVisitor<#interner>>(
                &self,
                visitor: &mut #traverser
            ) -> ::core::ops::ControlFlow<#traverser::BreakTy> {
                #body
                ::core::ops::ControlFlow::Continue(())
            }
        }
    }
}

pub fn traversable_derive<T: Traversable>(
    mut structure: synstructure::Structure<'_>,
) -> TokenStream {
    let ast = structure.ast();

    let interner = Interner::resolve(&ast.generics);
    let traverser = gen_param("T", &ast.generics);
    let traversable = T::traversable(&interner);

    structure.underscore_const(true);
    structure.add_bounds(synstructure::AddBounds::None);
    structure.bind_with(|_| synstructure::BindStyle::Move);

    if interner.lifetimes.is_empty() {
        structure.add_impl_generic(parse_quote! { 'tcx });
    }

    // If our derived implementation will be generic over the traversable type, then we must
    // constrain it to only those generic combinations that satisfy the traversable trait's
    // supertraits.
    if ast.generics.type_params().next().is_some() {
        let supertraits = T::supertraits(&interner);
        structure.add_where_predicate(parse_quote! { Self: #supertraits });
    }

    // We add predicates to each generic field type, rather than to our generic type parameters.
    // This results in a "perfect derive" that avoids having to propagate `#[skip_traversal]` annotations
    // into wrapping types, but it can result in trait solver cycles if any type parameters are involved
    // in recursive type definitions; fortunately that is not the case (yet).
    let mut predicates = HashSet::new();
    let arms = structure.each_variant(|variant| {
        T::arm(variant, |bind| {
            let ast = bind.ast();
            let field_ty = interner.type_of(&bind.referenced_ty_params(), [ast]);
            // we only need to add traversable predicate for generic types
            if field_ty == Generic {
                predicates.insert(ast.ty.clone());
            }
            T::traverse(bind.into_token_stream(), field_ty == Trivial)
        })
    });
    // the order in which `where` predicates appear in rust source is irrelevant
    #[allow(rustc::potential_query_instability)]
    for ty in predicates {
        structure.add_where_predicate(parse_quote! { #ty: #traversable });
    }
    let body = quote! { match self { #arms } };

    structure.bound_impl(traversable, T::impl_body(interner, traverser, body))
}
