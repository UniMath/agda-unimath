# The dependent universal property of set quotients

```agda
module foundation.dependent-universal-property-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.dependent-pair-types
open import foundation.dependent-reflecting-maps-equivalence-relations
open import foundation.equivalence-relations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.sets
```

</details>

## Idea

The {{#concept "dependent universal property of set quotients"}} is a unique characterization of dependent functions out of [set quotients](foundation.set-quotients.md). Given an [equivalence relation](foundation.equivalence-relations.md) `R` on a type `A` and a [reflecting map](foundation.reflecting-maps-equivalence-relations.md) `f : A → B` with respect to `R`, the dependent universal property of set quotients states that for any family of [sets](foundation.sets.md) `C` over `B` the map

```text
  ((y : B) → C y) → dependent-reflecting-map R f C
```

is an [equivalence](foundation-core.equivalences.md). The dependent universal property of set quotients looks more general than the [universal property of set quotients](foundation.universal-property-set-quotients.md), but is in fact equivalent to it.

## Definitions

### The dependent universal property of set quotients

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) {B : UU l3}
  (f : reflecting-map-equivalence-relation R B)
  where

  dependent-ev-set-quotient :
    {l4 : Level} {C : B → UU l4} (g : (y : B) → C y) →
    dependent-reflecting-map-equivalence-relation R f C
  pr1 (dependent-ev-set-quotient g) =
    g ∘ map-reflecting-map-equivalence-relation R f
  pr2 (dependent-ev-set-quotient g) r =
    apd g (reflects-map-reflecting-map-equivalence-relation R f r)

  dependent-universal-property-set-quotient : UUω
  dependent-universal-property-set-quotient =
    {l : Level} (C : B → Set l) →
    is-equiv (dependent-ev-set-quotient {l} {type-Set ∘ C})

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A) {B : UU l3}
  (f : reflecting-map-equivalence-relation R B)
  (H : dependent-universal-property-set-quotient R f)
  (C : B → Set l4)
  where

  induction-family-of-sets-set-quotient :
    dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) →
    (y : B) → type-Set (C y)
  induction-family-of-sets-set-quotient =
    map-inv-is-equiv (H C)

  compute-indunction-family-of-sets-set-quotient :
    (g : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    htpy-dependent-reflecting-map-equivalence-relation R f C
      ( dependent-ev-set-quotient R f (induction-family-of-sets-set-quotient g))
      ( g)
  compute-indunction-family-of-sets-set-quotient g =
    htpy-eq-dependent-reflecting-map-equivalence-relation R f C
      ( dependent-ev-set-quotient R f (induction-family-of-sets-set-quotient g))
      ( g)
      ( is-section-map-inv-is-equiv (H C) g)
```

## Properties

### A reflecting map `f : A → B` into a set satisfies the universal property of the set quotient if and only if it satisfies the dependent universal property

To prove that any reflecting map satisfying the universal property also satisfies the dependent universal property, consider the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
       ((y : B) → C y) ----------------> dependent-reflecting-map R f C
              |                                        |
            ≃ |                                        | ≃
              |                                        |
              ∨                                        ∨
  Σ (g : B → ΣBC), π∘g ~ id ------> Σ (g : reflecting-map R f ΣBC), π∘g ~ f/
```

By the universal property it follows that the bottom map is an equivalence, hence the top map is an equivalence.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  dependent-universal-property-universal-property-set-quotient :
    universal-property-set-quotient R B f →
    dependent-universal-property-set-quotient R f
  dependent-universal-property-universal-property-set-quotient H C =
    is-equiv-top-is-equiv-bottom-square
      ( λ g → (λ y → (y , g y) , refl-htpy' (id {A = type-Set B})))
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
```


## See also

- [The universal property of set quotients](foundation.universal-property-set-quotients.md)
