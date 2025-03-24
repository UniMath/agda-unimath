# Rewriting rules for pushouts

```agda
{-# OPTIONS --rewriting #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.rewriting-pushouts
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import reflection.rewriting

open import synthetic-homotopy-theory.cocones-under-spans funext
open import synthetic-homotopy-theory.dependent-cocones-under-spans funext univalence truncations
open import synthetic-homotopy-theory.pushouts funext univalence truncations
```

</details>

## Idea

This module endows the eliminator of the
[standard pushouts](synthetic-homotopy-theory.pushouts.md) `cogap` with strict
computation rules on the point constructors using Agda's
[rewriting](reflection.rewriting.md) functionality. This gives the strict
equalities

```text
  cogap (inl-pushout f g a) ≐ horizontal-map-cocone f g c a
```

and

```text
  cogap (inr-pushout f g b) ≐ vertical-map-cocone f g c b.
```

More generally, strict computation rules for the dependent eliminator are
enabled, giving the strict equalities

```text
  dependent-cogap (inl-pushout f g a) ≐
  horizontal-map-dependent-cocone f g (cocone-pushout f g) P c a
```

and

```text
  dependent-cogap (inr-pushout f g b) ≐
  vertical-map-dependent-cocone f g (cocone-pushout f g) P c b.
```

In addition, the pre-existing witnesses of these equalities:
`compute-inl-dependent-cogap`, `compute-inr-dependent-cogap`, and their
nondependent counterparts, reduce to `refl`. This is achieved using Agda's
[equality erasure](reflection.erasing-equality.md) functionality.

To enable these computation rules in your own formalizations, set the
`--rewriting` option and import this module. Keep in mind, however, that we
offer no way to selectively disable these rules, so if your module depends on
any other module that imports this one, you will automatically also have
rewriting for pushouts enabled.

By default, we abstain from using rewrite rules in agda-unimath. However, we
recognize their usefulness in, for instance, exploratory formalizations. Since
formalizations with and without rewrite rules can coexist, there is no harm in
providing these tools for those that see a need to use them. We do, however,
emphasize that formalizations without the use of rewrite rules are preferred
over those that do use them in the library, as the former can also be applied in
other formalizations that do not enable rewrite rules.

## Rewrite rules

```agda
{-# REWRITE compute-inl-dependent-cogap #-}
{-# REWRITE compute-inr-dependent-cogap #-}
```

## Properties

### Verifying the reduction behavior of the computation rules for the eliminators of standard pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {P : pushout f g → UU l4}
  (d : dependent-cocone f g (cocone-pushout f g) P)
  where

  _ : compute-inl-dependent-cogap f g d ~ refl-htpy
  _ = refl-htpy

  _ : compute-inr-dependent-cogap f g d ~ refl-htpy
  _ = refl-htpy

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  _ : compute-inl-cogap f g c ~ refl-htpy
  _ = refl-htpy

  _ : compute-inr-cogap f g c ~ refl-htpy
  _ = refl-htpy
```

## See also

- For some discussion on strict computation rules for higher inductive types,
  see the introduction to Section 6.2 of {{#cite UF13}}.

## References

{{#bibliography}}
