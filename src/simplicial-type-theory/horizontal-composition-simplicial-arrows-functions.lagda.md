# Horizontal composition of simplicial arrows of functions

```agda
module simplicial-type-theory.horizontal-composition-simplicial-arrows-functions where
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

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

Given a simplicial arrow `α` of functions `A → B` and a simplicial arrow `β` of
functions `B → C`, we may
{{#concept "horizontally compose" Disambiguation="simplicial arrows of functions" Agda=horizontal-comp-simplicial-arrow}}
them to obtain a simplicial arrow of functions `A → B`. The horizontal composite
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

  horizontal-comp-simplicial-arrow :
    simplicial-arrow (B → C) →
    simplicial-arrow (A → B) →
    simplicial-arrow (A → C)
  horizontal-comp-simplicial-arrow β α t x = β t (α t x)
```

## Properties

### Unit laws for horizontal composition of simplicial arrows of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-horizontal-comp-simplicial-arrow :
    (α : simplicial-arrow (A → B)) →
    horizontal-comp-simplicial-arrow (id-simplicial-arrow id) α ＝ α
  left-unit-law-horizontal-comp-simplicial-arrow α = refl

  right-unit-law-horizontal-comp-simplicial-arrow :
    (α : simplicial-arrow (A → B)) →
    horizontal-comp-simplicial-arrow α (id-simplicial-arrow id) ＝ α
  right-unit-law-horizontal-comp-simplicial-arrow α = refl
```

### Associativity of horizontal composition of simplicial arrows of functions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  associative-horizontal-comp-simplicial-arrow :
    (γ : simplicial-arrow (C → D))
    (β : simplicial-arrow (B → C))
    (α : simplicial-arrow (A → B)) →
    horizontal-comp-simplicial-arrow (horizontal-comp-simplicial-arrow γ β) α ＝
    horizontal-comp-simplicial-arrow γ (horizontal-comp-simplicial-arrow β α)
  associative-horizontal-comp-simplicial-arrow γ β α = refl
```
