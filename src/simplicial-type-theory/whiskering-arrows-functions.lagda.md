# Whiskering operations on simplicial arrows of functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.whiskering-arrows-functions
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.horizontal-composition-arrows-functions I
```

</details>

## Idea

Given a simplicial arrow `α` of functions `A → B` we may whisker it on the left
by a function `f : B → C` to obtain a simplicial arrow of functions `A → C`, or
we may whisker it on the right by a function `g : C → A` to obtain a simplicial
arrow of functions `C → B`.

## Definitions

### Left whiskering simplicial arrows of functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisker-comp-arrow▵ :
    (B → C) → arrow▵ (A → B) → arrow▵ (A → C)
  left-whisker-comp-arrow▵ f =
    horizontal-comp-arrow▵ (id-arrow▵ f)
```

### Right whiskering simplicial arrows of functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-whisker-comp-arrow▵ :
    arrow▵ (B → C) → (A → B) → arrow▵ (A → C)
  right-whisker-comp-arrow▵ β g =
    horizontal-comp-arrow▵ β (id-arrow▵ g)
```

## Properties

### Unit laws of whiskering of simplicial arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-left-whisker-comp-arrow▵ :
    (α : arrow▵ (A → B)) →
    left-whisker-comp-arrow▵ id α ＝ α
  left-unit-law-left-whisker-comp-arrow▵ =
    left-unit-law-horizontal-comp-arrow▵

  right-unit-law-right-whisker-comp-arrow▵ :
    (α : arrow▵ (A → B)) →
    right-whisker-comp-arrow▵ α id ＝ α
  right-unit-law-right-whisker-comp-arrow▵ =
    right-unit-law-horizontal-comp-arrow▵
```

### Absorption laws of whiskering of simplicial arrows

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-absorption-law-left-whisker-comp-arrow▵ :
    (g : B → C) (f : A → B) →
    left-whisker-comp-arrow▵ g (id-arrow▵ f) ＝
    id-arrow▵ (g ∘ f)
  right-absorption-law-left-whisker-comp-arrow▵ g f = refl

  left-absorption-law-right-whisker-comp-arrow▵ :
    (g : B → C) (f : A → B) →
    right-whisker-comp-arrow▵ (id-arrow▵ g) f ＝
    id-arrow▵ (g ∘ f)
  left-absorption-law-right-whisker-comp-arrow▵ g f = refl
```

### Whiskering of simplicial arrows between functions preserves function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  preserves-comp-left-whisker-comp-arrow▵ :
    (h : C → D) (g : B → C) (α : arrow▵ (A → B)) →
    left-whisker-comp-arrow▵ (h ∘ g) α ＝
    left-whisker-comp-arrow▵ h
      ( left-whisker-comp-arrow▵ g α)
  preserves-comp-left-whisker-comp-arrow▵ h g α = refl

  preserves-comp-right-whisker-comp-arrow▵ :
    (α : arrow▵ (C → D)) (g : B → C) (f : A → B) →
    right-whisker-comp-arrow▵ α (g ∘ f) ＝
    right-whisker-comp-arrow▵
      ( right-whisker-comp-arrow▵ α g)
      ( f)
  preserves-comp-right-whisker-comp-arrow▵ h g α = refl
```
