use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use smallvec::SmallVec;
use std::{
    collections::{hash_map::Entry, HashMap, VecDeque},
    mem,
};
use syn::{
    meta::ParseNestedMeta,
    parse::Error,
    parse_quote,
    spanned::Spanned,
    visit::{self, Visit},
    Attribute, DeriveInput, Field, Generics, Lifetime, LitStr, Variant,
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

#[derive(Clone, Copy, Debug, PartialEq)]
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

#[derive(Default)]
struct SkipTraversalValidator {
    at_valid_location: bool,
    invalid: Vec<Span>,
}

impl Visit<'_> for SkipTraversalValidator {
    // ported from visit::visit_derive_input, but at valid location when visiting attributes
    fn visit_derive_input(&mut self, i: &DeriveInput) {
        self.at_valid_location = true;
        for it in &i.attrs {
            self.visit_attribute(it);
        }
        self.at_valid_location = false;
        self.visit_visibility(&i.vis);
        self.visit_ident(&i.ident);
        self.visit_generics(&i.generics);
        self.visit_data(&i.data);
    }

    // ported from visit::visit_field, but at valid location when visiting attributes
    fn visit_field(&mut self, i: &Field) {
        self.at_valid_location = true;
        for it in &i.attrs {
            self.visit_attribute(it);
        }
        self.at_valid_location = false;
        self.visit_visibility(&i.vis);
        self.visit_field_mutability(&i.mutability);
        if let Some(it) = &i.ident {
            self.visit_ident(it);
        }
        //skip!(i.colon_token);
        self.visit_type(&i.ty);
    }

    // ported from visit::visit_variant, but at valid location when visiting attributes
    fn visit_variant(&mut self, i: &Variant) {
        self.at_valid_location = true;
        for it in &i.attrs {
            self.visit_attribute(it);
        }
        self.at_valid_location = false;
        self.visit_ident(&i.ident);
        self.visit_fields(&i.fields);
        if let Some(it) = &i.discriminant {
            // skip!((it).0);
            self.visit_expr(&(it).1);
        }
    }

    fn visit_attribute(&mut self, i: &Attribute) {
        let at_valid_location = mem::replace(&mut self.at_valid_location, false);
        if !at_valid_location && i.path().is_ident("skip_traversal") {
            self.invalid.push(i.span());
        }
        visit::visit_attribute(self, i);
        self.at_valid_location = at_valid_location;
    }
}

impl SkipTraversalValidator {
    fn validate(derive_input: &DeriveInput) -> Result<(), Error> {
        let mut validator = Self::default();
        validator.visit_derive_input(derive_input);
        let mut errors = validator.invalid.into_iter().map(|span| {
            Error::new(
                span,
                "#[skip_traversal] attributes are only valid on items, variants and fields",
            )
        });
        if let Some(mut error) = errors.next() {
            error.extend(errors);
            Err(error)
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum WhenToSkip {
    /// No skip_traversal annotation requires the annotated item to be skipped
    Never,

    /// A skip_traversal annotation requires the annotated item to be skipped, with its type
    /// constrained to TriviallyTraversable
    Always(Span),

    /// A `despite_potential_miscompilation_because` annotation is present, thus requiring the
    /// annotated item to be forcibly skipped without its type being constrained to
    /// TriviallyTraversable
    Forced,
}
use WhenToSkip::*;

impl Default for WhenToSkip {
    fn default() -> Self {
        Never
    }
}

impl PartialEq for WhenToSkip {
    fn eq(&self, other: &Self) -> bool {
        mem::discriminant(self) == mem::discriminant(other)
    }
}

impl std::ops::BitOrAssign for WhenToSkip {
    fn bitor_assign(&mut self, rhs: Self) {
        match self {
            Forced => (),
            Always(_) => {
                if rhs == Forced {
                    *self = Forced;
                }
            }
            Never => *self = rhs,
        }
    }
}

impl WhenToSkip {
    fn is_skipped(&self) -> bool {
        *self != Never
    }

    fn check_for_conflicts(&mut self, other: Self, ty: &syn::Type) -> Result<(), Error> {
        if *self != other && let (Always(span), _) | (_, Always(span)) = (*self, other) {
            Err(Error::new(
                span,
                format!(
                    "\
                This annotation only makes sense if all fields of type `{0}` are annotated identically.\n\
                In particular, the derived impl will only be applicable when `{0}: TriviallyTraversable` and therefore all traversals of `{0}` will be no-ops;\n\
                accordingly it makes no sense for other fields of type `{0}` to omit `#[skip_traversal]`.\
            ",
                    ty.to_token_stream(),
                ),
            ))
        } else {
            *self |= other;
            Ok(())
        }
    }

    fn find<const IS_TYPE: bool>(&mut self, attrs: &[Attribute], ty: Type) -> Result<(), Error> {
        fn parse_reason(meta: &ParseNestedMeta<'_>) -> Result<(), Error> {
            if !meta.value()?.parse::<LitStr>()?.value().trim().is_empty() {
                Ok(())
            } else {
                Err(meta.error("skip reason must be a non-empty string"))
            }
        }

        let mut found = None;
        for attr in attrs {
            if attr.path().is_ident("skip_traversal") {
                if !IS_TYPE && ty == Trivial {
                    return Err(Error::new_spanned(
                        attr,
                        "guaranteed trivial fields are always skipped, so this attribute is superfluous",
                    ));
                }

                attr.parse_nested_meta(|meta| {
                    if meta.path.is_ident("but_impl_despite_trivial_because") {
                        return if IS_TYPE && ty == Trivial {
                            parse_reason(&meta)?;
                            *self |= Always(meta.error("").span());
                            Ok(())
                        } else {
                            Err(meta.error("`but_impl_despite_trivial_because` is only valid on guaranteed trivial types"))
                        };
                    }

                    if meta.path.is_ident("because_trivial") {
                        return if !IS_TYPE {
                            debug_assert_ne!(ty, Trivial);
                            *self |= Always(meta.error("").span());
                            Ok(())
                        } else {
                            Err(meta
                                .error("`because_trivial` is only valid on potentially non-trivial variants or fields"))
                        };
                    }

                    if meta.path.is_ident("despite_potential_miscompilation_because") {
                        parse_reason(&meta)?;
                        if ty != Trivial {
                            *self |= Forced;
                            return Ok(());
                        }
                    }

                    Err(meta.error("unsupported skip reason"))
                })?;
                found = Some(attr);
            }
        }

        if self.is_skipped() {
            Ok(())
        } else if IS_TYPE && ty == Trivial {
            Err(Error::new(
                Span::call_site(),
                "\
                Traversal of guaranteed trivial types are no-ops by default, so explicitly deriving the traversable traits for them is rarely necessary.\n\
                If the need has arisen to due the appearance of this type in an anonymous tuple, consider replacing that tuple with a named struct;\n\
                otherwise add `#[skip_traversal(but_impl_despite_trivial_because = \"<reason for implementation>\")]` to this type.\
            ",
            ))
        } else if let Some(attr) = found {
            Err(Error::new_spanned(
                attr,
                if IS_TYPE {
                    "\
                    Justification must be provided for skipping potentially non-trivial types, by specifying\n\
                    `despite_potential_miscompilation_because = \"<reason>\"`\
                "
                } else {
                    "\
                    Justification must be provided for skipping potentially non-trivial fields, by specifying EITHER:\n\
                    `because_trivial` if concrete instances are in fact trivial (enforced by requiring the type to implement `TriviallyTraversable`); OR\n\
                    `despite_potential_miscompilation_because = \"<reason>\"` in the rare case that a field should always be skipped regardless\
                "
                },
            ))
        } else {
            Ok(())
        }
    }
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
        f: impl FnMut(&synstructure::BindingInfo<'_>) -> Result<TokenStream, Error>,
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
        quote! { ::rustc_type_ir::fold::TypeFoldable<#interner> }
    }
    fn supertraits(interner: &Interner<'_>) -> TokenStream {
        Visitable::traversable(interner)
    }
    fn traverse(bind: TokenStream, noop: bool) -> TokenStream {
        if noop {
            bind
        } else {
            quote! { ::rustc_type_ir::fold::TypeFoldable::try_fold_with(#bind, folder)? }
        }
    }
    fn arm(
        variant: &synstructure::VariantInfo<'_>,
        mut f: impl FnMut(&synstructure::BindingInfo<'_>) -> Result<TokenStream, Error>,
    ) -> TokenStream {
        let bindings = variant.bindings();
        variant.construct(|_, index| f(&bindings[index]).unwrap_or_else(Error::into_compile_error))
    }
    fn impl_body(
        interner: Interner<'_>,
        traverser: impl ToTokens,
        body: impl ToTokens,
    ) -> TokenStream {
        quote! {
            fn try_fold_with<#traverser: ::rustc_type_ir::fold::FallibleTypeFolder<#interner>>(
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
        quote! { ::rustc_type_ir::visit::TypeVisitable<#interner> }
    }
    fn supertraits(_: &Interner<'_>) -> TokenStream {
        quote! { ::core::clone::Clone + ::core::fmt::Debug }
    }
    fn traverse(bind: TokenStream, noop: bool) -> TokenStream {
        if noop {
            quote! {}
        } else {
            quote! { ::rustc_type_ir::visit::TypeVisitable::visit_with(#bind, visitor)?; }
        }
    }
    fn arm(
        variant: &synstructure::VariantInfo<'_>,
        f: impl FnMut(&synstructure::BindingInfo<'_>) -> Result<TokenStream, Error>,
    ) -> TokenStream {
        variant
            .bindings()
            .iter()
            .map(f)
            .collect::<Result<_, _>>()
            .unwrap_or_else(Error::into_compile_error)
    }
    fn impl_body(
        interner: Interner<'_>,
        traverser: impl ToTokens,
        body: impl ToTokens,
    ) -> TokenStream {
        quote! {
            fn visit_with<#traverser: ::rustc_type_ir::visit::TypeVisitor<#interner>>(
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
) -> Result<TokenStream, Error> {
    let ast = structure.ast();
    SkipTraversalValidator::validate(ast)?;

    let interner = Interner::resolve(&ast.generics);
    let traverser = gen_param("T", &ast.generics);
    let traversable = T::traversable(&interner);
    let trivial = |ty| parse_quote! { #interner: ::rustc_type_ir::TriviallyTraverses<#ty> };

    structure.underscore_const(true);
    structure.add_bounds(synstructure::AddBounds::None);
    structure.bind_with(|_| synstructure::BindStyle::Move);

    let not_generic = if interner.lifetimes.is_empty() {
        structure.add_impl_generic(parse_quote! { 'tcx });
        Trivial
    } else {
        Internable
    };

    // If our derived implementation will be generic over the traversable type, then we must
    // constrain it to only those generic combinations that satisfy the traversable trait's
    // supertraits.
    let ty = if ast.generics.type_params().next().is_some() {
        let supertraits = T::supertraits(&interner);
        structure.add_where_predicate(parse_quote! { Self: #supertraits });
        Generic
    } else {
        not_generic
    };

    let mut when_to_skip = WhenToSkip::default();
    when_to_skip.find::<true>(&ast.attrs, ty)?;
    let body = if when_to_skip.is_skipped() {
        T::traverse(quote! { self }, true)
    } else {
        // We add predicates to each generic field type, rather than to our generic type parameters.
        // This results in a "perfect derive" that avoids having to propagate `#[skip_traversal]` annotations
        // into wrapping types, but it can result in trait solver cycles if any type parameters are involved
        // in recursive type definitions; fortunately that is not the case (yet).
        let mut predicates = HashMap::<_, (WhenToSkip, _)>::new();
        let arms = structure.each_variant(|variant| {
            let variant_ty =
                interner.type_of(&variant.referenced_ty_params(), variant.ast().fields);
            let mut skipped_variant = WhenToSkip::default();
            if let Err(error) = skipped_variant.find::<false>(variant.ast().attrs, variant_ty) {
                return error.into_compile_error();
            }
            T::arm(variant, |bind| {
                let ast = bind.ast();
                let field_ty = interner.type_of(&bind.referenced_ty_params(), [ast]);
                let mut skipped_field = skipped_variant;
                skipped_field.find::<false>(&ast.attrs, field_ty)?;

                let is_skipped = field_ty == Trivial || {
                    match predicates.entry(ast.ty.clone()) {
                        Entry::Occupied(existing) => {
                            existing.into_mut().0.check_for_conflicts(skipped_field, &ast.ty)?
                        }
                        Entry::Vacant(slot) => {
                            slot.insert((skipped_field, field_ty));
                        }
                    }
                    skipped_field.is_skipped()
                };

                Ok(T::traverse(bind.into_token_stream(), is_skipped))
            })
        });
        // the order in which `where` predicates appear in rust source is irrelevant
        #[allow(rustc::potential_query_instability)]
        for (ty, (when_to_skip, field_ty)) in predicates {
            let predicate = match when_to_skip {
                Always(_) => trivial(ty),
                // we only need to add traversable predicate for generic types
                Never if field_ty == Generic => parse_quote! { #ty: #traversable },
                _ => continue,
            };
            structure.add_where_predicate(predicate);
        }
        quote! { match self { #arms } }
    };

    Ok(structure.bound_impl(traversable, T::impl_body(interner, traverser, body)))
}
