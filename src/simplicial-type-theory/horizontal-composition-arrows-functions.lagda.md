# Horizontal composition of arrows in functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.horizontal-composition-arrows-functions
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
```

</details>

## Idea

Given a [simplicial arrow](simplicial-type-theory.arrows.md) `α` of functions
`A → B` and a simplicial arrow `β` of functions `B → C`, we may
{{#concept "horizontally compose" Disambiguation="simplicial arrows of functions" Agda=horizontal-comp-arrow▵}}
them to obtain a simplicial arrow of functions `A → C`. The horizontal composite
is constructed by "synchronously traversing `α` and `β`":

```text
  β □ α := (t ↦ x ↦ β t (α t x)),
```

and thus satisfies unit laws and associativity strictly.

## Definitions

### Horizontal composition of simplicial arrows of functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  horizontal-comp-arrow▵ :
    arrow▵ (B → C) → arrow▵ (A → B) → arrow▵ (A → C)
  horizontal-comp-arrow▵ β α t x = β t (α t x)
```

## Properties

### Unit laws for horizontal composition of simplicial arrows of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-horizontal-comp-arrow▵ :
    (α : arrow▵ (A → B)) →
    horizontal-comp-arrow▵ (id-arrow▵ id) α ＝ α
  left-unit-law-horizontal-comp-arrow▵ α = refl

  right-unit-law-horizontal-comp-arrow▵ :
    (α : arrow▵ (A → B)) →
    horizontal-comp-arrow▵ α (id-arrow▵ id) ＝ α
  right-unit-law-horizontal-comp-arrow▵ α = refl
```

### Associativity of horizontal composition of simplicial arrows of functions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  associative-horizontal-comp-arrow▵ :
    (γ : arrow▵ (C → D))
    (β : arrow▵ (B → C))
    (α : arrow▵ (A → B)) →
    horizontal-comp-arrow▵ (horizontal-comp-arrow▵ γ β) α ＝
    horizontal-comp-arrow▵ γ (horizontal-comp-arrow▵ β α)
  associative-horizontal-comp-arrow▵ γ β α = refl
```
