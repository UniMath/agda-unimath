# Whiskering operations on natural transformations between functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.whiskering-natural-transformations-functions
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
open import simplicial-type-theory.horizontal-composition-directed-edges-functions I
open import simplicial-type-theory.horizontal-composition-natural-transformations I
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.whiskering-directed-edges-functions I
```

</details>

## Idea

Given a
[natural transformation](simplicial-type-theory.natural-transformations.md)
`α : f ⇒▵ f'` of functions from `A` to `B` we may
{{#concept "left whisker" Disambiguation="natural transformation by function" Agda=left-whisker-comp-natural-transformation▵}}
by a function `h : B → C` to obtain a natural transformation `hα : hf ⇒▵ hf'`,
or we may
{{#concept "right whisker" Disambiguation="natural transformation by function" Agda=right-whisker-comp-natural-transformation▵}}
by a function `g : C → A` to obtain a natural-transformation of functions
`αg : fg ⇒▵ f'g`.

## Definitions

### Left whiskering natural transformations between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisker-comp-natural-transformation▵ :
    (h : B → C) {f f' : A → B} → (f ⇒▵ f') → (h ∘ f ⇒▵ h ∘ f')
  left-whisker-comp-natural-transformation▵ h α x =
    ( h ∘ family-of-arrows-natural-transformation▵ α x ,
      ap h (eq-source-natural-transformation▵ α x) ,
      ap h (eq-target-natural-transformation▵ α x))
```

### Right whiskering natural transformations between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-whisker-comp-natural-transformation▵ :
    {f f' : A → B} → (f ⇒▵ f') → (g : C → A) → (f ∘ g ⇒▵ f' ∘ g)
  right-whisker-comp-natural-transformation▵ α g =
    horizontal-comp-natural-transformation▵ α (id-natural-transformation▵ g)
```

## Properties

### Unit laws of whiskering of natural transformations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-left-whisker-comp-natural-transformation▵ :
    {f f' : A → B} (α : f ⇒▵ f') →
    left-whisker-comp-natural-transformation▵ id α ＝ α
  left-unit-law-left-whisker-comp-natural-transformation▵ α =
    eq-htpy-natural-transformation▵
      ( left-whisker-comp-natural-transformation▵ id α)
      ( α)
      ( λ x →
        ( refl-htpy ,
          ap-id (eq-source-natural-transformation▵ α x) ,
          ap-id (eq-target-natural-transformation▵ α x)))

  right-unit-law-right-whisker-comp-natural-transformation▵ :
    {f f' : A → B} (α : f ⇒▵ f') →
    right-whisker-comp-natural-transformation▵ α id ＝ α
  right-unit-law-right-whisker-comp-natural-transformation▵ =
    right-unit-law-horizontal-comp-natural-transformation▵
```

### Absorption laws of whiskering of natural transformations

These laws hold strictly.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-absorption-law-left-whisker-comp-natural-transformation▵ :
    (g : B → C) (f : A → B) →
    left-whisker-comp-natural-transformation▵
      ( g)
      ( id-natural-transformation▵ f) ＝
    id-natural-transformation▵ (g ∘ f)
  right-absorption-law-left-whisker-comp-natural-transformation▵ g f = refl

  left-absorption-law-right-whisker-comp-natural-transformation▵ :
    (g : B → C) (f : A → B) →
    right-whisker-comp-natural-transformation▵
      ( id-natural-transformation▵ g)
      ( f) ＝
    id-natural-transformation▵ (g ∘ f)
  left-absorption-law-right-whisker-comp-natural-transformation▵ g f = refl
```

### Whiskering of natural transformations between functions preserves function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  preserves-comp-left-whisker-comp-natural-transformation▵ :
    (h : C → D) (g : B → C) {f f' : A → B} (α : f ⇒▵ f') →
    left-whisker-comp-natural-transformation▵ (h ∘ g) α ＝
    left-whisker-comp-natural-transformation▵
      ( h)
      ( left-whisker-comp-natural-transformation▵ g α)
  preserves-comp-left-whisker-comp-natural-transformation▵ h g α =
    eq-htpy-natural-transformation▵
      ( left-whisker-comp-natural-transformation▵ (h ∘ g) α)
      ( left-whisker-comp-natural-transformation▵ h
        ( left-whisker-comp-natural-transformation▵ g α))
      ( λ x →
        ( refl-htpy ,
          ap-comp h g (eq-source-natural-transformation▵ α x) ,
          ap-comp h g (eq-target-natural-transformation▵ α x)))

  preserves-comp-right-whisker-comp-natural-transformation▵ :
    {h h' : C → D} (α : h ⇒▵ h') (g : B → C) (f : A → B) →
    right-whisker-comp-natural-transformation▵ α (g ∘ f) ＝
    right-whisker-comp-natural-transformation▵
      ( right-whisker-comp-natural-transformation▵ α g)
      ( f)
  preserves-comp-right-whisker-comp-natural-transformation▵ α g f = refl
```
