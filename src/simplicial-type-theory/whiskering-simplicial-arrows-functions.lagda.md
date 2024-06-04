# Whiskering operations on simplicial arrows of functions

```agda
module simplicial-type-theory.whiskering-simplicial-arrows-functions where
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

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.horizontal-composition-simplicial-arrows-functions
open import simplicial-type-theory.simplicial-arrows
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

  left-whisker-comp-simplicial-arrow :
    (B → C) → simplicial-arrow (A → B) → simplicial-arrow (A → C)
  left-whisker-comp-simplicial-arrow f =
    horizontal-comp-simplicial-arrow (id-simplicial-arrow f)
```

### Right whiskering simplicial arrows of functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-whisker-comp-simplicial-arrow :
    simplicial-arrow (B → C) → (A → B) → simplicial-arrow (A → C)
  right-whisker-comp-simplicial-arrow β g =
    horizontal-comp-simplicial-arrow β (id-simplicial-arrow g)
```

## Properties

### Unit laws of whiskering of simplicial arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-left-whisker-comp-simplicial-arrow :
    (α : simplicial-arrow (A → B)) →
    left-whisker-comp-simplicial-arrow id α ＝ α
  left-unit-law-left-whisker-comp-simplicial-arrow =
    left-unit-law-horizontal-comp-simplicial-arrow

  right-unit-law-right-whisker-comp-simplicial-arrow :
    (α : simplicial-arrow (A → B)) →
    right-whisker-comp-simplicial-arrow α id ＝ α
  right-unit-law-right-whisker-comp-simplicial-arrow =
    right-unit-law-horizontal-comp-simplicial-arrow
```

### Absorption laws of whiskering of simplicial arrows

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-absorption-law-left-whisker-comp-simplicial-arrow :
    (g : B → C) (f : A → B) →
    left-whisker-comp-simplicial-arrow g (id-simplicial-arrow f) ＝
    id-simplicial-arrow (g ∘ f)
  right-absorption-law-left-whisker-comp-simplicial-arrow g f = refl

  left-absorption-law-right-whisker-comp-simplicial-arrow :
    (g : B → C) (f : A → B) →
    right-whisker-comp-simplicial-arrow (id-simplicial-arrow g) f ＝
    id-simplicial-arrow (g ∘ f)
  left-absorption-law-right-whisker-comp-simplicial-arrow g f = refl
```

### Whiskering of simplicial arrows between functions preserves function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  preserves-comp-left-whisker-comp-simplicial-arrow :
    (h : C → D) (g : B → C) (α : simplicial-arrow (A → B)) →
    left-whisker-comp-simplicial-arrow (h ∘ g) α ＝
    left-whisker-comp-simplicial-arrow h
      ( left-whisker-comp-simplicial-arrow g α)
  preserves-comp-left-whisker-comp-simplicial-arrow h g α = refl

  preserves-comp-right-whisker-comp-simplicial-arrow :
    (α : simplicial-arrow (C → D)) (g : B → C) (f : A → B) →
    right-whisker-comp-simplicial-arrow α (g ∘ f) ＝
    right-whisker-comp-simplicial-arrow
      ( right-whisker-comp-simplicial-arrow α g)
      ( f)
  preserves-comp-right-whisker-comp-simplicial-arrow h g α = refl
```
