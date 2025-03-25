# Diagonal maps of types

```agda
module foundation.diagonal-maps-of-types where

open import foundation-core.diagonal-maps-of-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

The
{{#concept "diagonal map" Disambiguation="of a type into exponentials" Agda=diagonal-exponential}}
of a type `A` is the map that includes the points of `A` into the exponential
`X → A`.

## Properties

### The action on identifications of an (exponential) diagonal is a diagonal

```agda
module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (x y : B)
  where

  compute-eq-htpy-ap-diagonal-exponential :
    ap (diagonal-exponential B A) ~ eq-htpy ∘ diagonal-exponential (x ＝ y) A
  compute-eq-htpy-ap-diagonal-exponential p =
    map-eq-transpose-equiv
      ( equiv-funext)
      ( compute-htpy-eq-ap-diagonal-exponential A x y p)
```

### Computing the fibers of diagonal maps

```agda
compute-fiber-diagonal-exponential :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  fiber (diagonal-exponential B A) f ≃ Σ B (λ b → (x : A) → b ＝ f x)
compute-fiber-diagonal-exponential f = equiv-tot (λ _ → equiv-funext)
```
