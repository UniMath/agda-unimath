# Diagonal maps of types

```agda
module foundation.diagonal-maps-of-types where
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

## Definitions

```agda
module _
  {l1 l2 : Level} (A : UU l1) (X : UU l2)
  where

  diagonal-exponential : A → X → A
  diagonal-exponential = const X
```

## Properties

### The action on identifications of a diagonal map is another diagonal map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (x y : A) (B : UU l2)
  where

  htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eq :
    htpy-eq ∘ ap (diagonal-exponential A B) ~ diagonal-exponential (x ＝ y) B
  htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eq refl = refl

  htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Id :
    diagonal-exponential (x ＝ y) B ~ htpy-eq ∘ ap (diagonal-exponential A B)
  htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Id =
    inv-htpy htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eq
```

### Given an element of the exponent the diagonal map is injective

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (b : B)
  where

  is-injective-diagonal-exponential :
    is-injective (diagonal-exponential A B)
  is-injective-diagonal-exponential p = htpy-eq p b

  diagonal-exponential-injection : injection A (B → A)
  pr1 diagonal-exponential-injection = diagonal-exponential A B
  pr2 diagonal-exponential-injection = is-injective-diagonal-exponential
```

### The action on identifications of an (exponential) diagonal is a diagonal

```agda
module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (x y : B)
  where

  compute-htpy-eq-ap-diagonal-exponential :
    htpy-eq ∘ ap (diagonal-exponential B A) ~ diagonal-exponential (x ＝ y) A
  compute-htpy-eq-ap-diagonal-exponential refl = refl

  inv-compute-htpy-eq-ap-diagonal-exponential :
    diagonal-exponential (x ＝ y) A ~ htpy-eq ∘ ap (diagonal-exponential B A)
  inv-compute-htpy-eq-ap-diagonal-exponential =
    inv-htpy compute-htpy-eq-ap-diagonal-exponential

  compute-eq-htpy-ap-diagonal-exponential :
    ap (diagonal-exponential B A) ~ eq-htpy ∘ diagonal-exponential (x ＝ y) A
  compute-eq-htpy-ap-diagonal-exponential p =
    map-eq-transpose-equiv
      ( equiv-funext)
      ( compute-htpy-eq-ap-diagonal-exponential p)
```

### Computing the fibers of diagonal maps

```agda
compute-fiber-diagonal-exponential :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  fiber (diagonal-exponential B A) f ≃ Σ B (λ b → (x : A) → b ＝ f x)
compute-fiber-diagonal-exponential f = equiv-tot (λ _ → equiv-funext)
```
