# Structured types

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the structured types namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import structured-types.cartesian-products-types-equipped-with-endomorphisms funext univalence public
open import structured-types.central-h-spaces funext public
open import structured-types.commuting-squares-of-pointed-homotopies funext univalence truncations public
open import structured-types.commuting-squares-of-pointed-maps funext univalence truncations public
open import structured-types.commuting-triangles-of-pointed-maps funext univalence truncations public
open import structured-types.conjugation-pointed-types funext univalence truncations public
open import structured-types.constant-pointed-maps funext univalence truncations public
open import structured-types.contractible-pointed-types funext univalence public
open import structured-types.cyclic-types funext univalence truncations public
open import structured-types.dependent-products-h-spaces funext univalence truncations public
open import structured-types.dependent-products-pointed-types public
open import structured-types.dependent-products-wild-monoids funext univalence truncations public
open import structured-types.dependent-types-equipped-with-automorphisms funext univalence truncations public
open import structured-types.equivalences-h-spaces funext univalence truncations public
open import structured-types.equivalences-pointed-arrows funext univalence truncations public
open import structured-types.equivalences-types-equipped-with-automorphisms funext univalence truncations public
open import structured-types.equivalences-types-equipped-with-endomorphisms funext univalence truncations public
open import structured-types.faithful-pointed-maps funext univalence truncations public
open import structured-types.fibers-of-pointed-maps funext univalence truncations public
open import structured-types.finite-multiplication-magmas funext univalence truncations public
open import structured-types.function-h-spaces funext univalence truncations public
open import structured-types.function-magmas funext univalence public
open import structured-types.function-wild-monoids funext univalence truncations public
open import structured-types.h-spaces funext univalence truncations public
open import structured-types.initial-pointed-type-equipped-with-automorphism funext univalence truncations public
open import structured-types.involutive-type-of-h-space-structures funext univalence truncations public
open import structured-types.involutive-types funext univalence truncations public
open import structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms funext univalence public
open import structured-types.iterated-pointed-cartesian-product-types funext univalence truncations public
open import structured-types.magmas funext univalence public
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms funext univalence truncations public
open import structured-types.morphisms-h-spaces funext univalence truncations public
open import structured-types.morphisms-magmas funext univalence public
open import structured-types.morphisms-pointed-arrows funext univalence truncations public
open import structured-types.morphisms-twisted-pointed-arrows funext univalence truncations public
open import structured-types.morphisms-types-equipped-with-automorphisms funext univalence truncations public
open import structured-types.morphisms-types-equipped-with-endomorphisms funext univalence truncations public
open import structured-types.morphisms-wild-monoids funext univalence truncations public
open import structured-types.noncoherent-h-spaces funext public
open import structured-types.opposite-pointed-spans funext univalence truncations public
open import structured-types.pointed-2-homotopies funext univalence truncations public
open import structured-types.pointed-cartesian-product-types funext univalence truncations public
open import structured-types.pointed-dependent-functions funext public
open import structured-types.pointed-dependent-pair-types public
open import structured-types.pointed-equivalences funext univalence truncations public
open import structured-types.pointed-families-of-types public
open import structured-types.pointed-homotopies funext univalence truncations public
open import structured-types.pointed-isomorphisms funext univalence truncations public
open import structured-types.pointed-maps funext univalence truncations public
open import structured-types.pointed-retractions funext univalence truncations public
open import structured-types.pointed-sections funext univalence truncations public
open import structured-types.pointed-span-diagrams funext univalence truncations public
open import structured-types.pointed-spans funext univalence truncations public
open import structured-types.pointed-types public
open import structured-types.pointed-types-equipped-with-automorphisms funext univalence truncations public
open import structured-types.pointed-unit-type funext univalence truncations public
open import structured-types.pointed-universal-property-contractible-types funext univalence truncations public
open import structured-types.postcomposition-pointed-maps funext univalence truncations public
open import structured-types.precomposition-pointed-maps funext univalence truncations public
open import structured-types.sets-equipped-with-automorphisms funext univalence public
open import structured-types.small-pointed-types funext univalence truncations public
open import structured-types.symmetric-elements-involutive-types funext univalence truncations public
open import structured-types.symmetric-h-spaces funext univalence truncations public
open import structured-types.transposition-pointed-span-diagrams funext univalence truncations public
open import structured-types.types-equipped-with-automorphisms funext univalence public
open import structured-types.types-equipped-with-endomorphisms funext univalence public
open import structured-types.uniform-pointed-homotopies funext univalence truncations public
open import structured-types.universal-property-pointed-equivalences funext univalence truncations public
open import structured-types.unpointed-maps public
open import structured-types.whiskering-pointed-2-homotopies-concatenation funext univalence truncations public
open import structured-types.whiskering-pointed-homotopies-composition funext univalence truncations public
open import structured-types.wild-category-of-pointed-types funext univalence truncations public
open import structured-types.wild-groups funext univalence truncations public
open import structured-types.wild-loops funext univalence truncations public
open import structured-types.wild-monoids funext univalence truncations public
open import structured-types.wild-quasigroups funext univalence public
open import structured-types.wild-semigroups funext univalence public
```
