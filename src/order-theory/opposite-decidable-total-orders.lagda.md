# Opposite decidable total orders

```agda
module order-theory.opposite-decidable-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.greatest-lower-bounds-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.opposite-posets
open import order-theory.posets
```

</details>

## Idea

Let `X` be a [decidable total order](order-theory.decidable-total-orders.md).
Its
{{#concept "opposite" Disambiguation="decidable total order" Agda=opposite-Decidable-Total-Order}}
`Xᵒᵖ` is given by reversing the relation.

## Definition

### The opposite decidable total order

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  poset-opposite-Decidable-Total-Order : Poset l1 l2
  poset-opposite-Decidable-Total-Order =
    opposite-Poset (poset-Decidable-Total-Order X)

  is-decidable-total-poset-opposite-Decidable-Total-Order :
    is-decidable-total-Poset poset-opposite-Decidable-Total-Order
  is-decidable-total-poset-opposite-Decidable-Total-Order =
    ( ( λ x y → is-total-poset-Decidable-Total-Order X y x) ,
      ( λ x y → is-decidable-poset-Decidable-Total-Order X y x))

  opposite-Decidable-Total-Order : Decidable-Total-Order l1 l2
  opposite-Decidable-Total-Order =
    ( poset-opposite-Decidable-Total-Order ,
      is-decidable-total-poset-opposite-Decidable-Total-Order)
```

## Properties

### The maximum of two elements in a decidable total order is their minimum in the opposite decidable total order

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  (a b : type-Decidable-Total-Order X)
  where

  abstract
    min-opposite-Decidable-Total-Order :
      min-Decidable-Total-Order
        ( opposite-Decidable-Total-Order X)
        ( a)
        ( b) ＝
      max-Decidable-Total-Order X a b
    min-opposite-Decidable-Total-Order =
      ap pr1
        ( all-elements-equal-has-least-binary-upper-bound-Poset
          ( poset-Decidable-Total-Order X)
          ( a)
          ( b)
          ( has-greatest-binary-lower-bound-Decidable-Total-Order
            ( opposite-Decidable-Total-Order X)
            ( a)
            ( b))
          ( has-least-binary-upper-bound-Decidable-Total-Order X a b))

    max-opposite-Decidable-Total-Order :
      max-Decidable-Total-Order
        ( opposite-Decidable-Total-Order X)
        ( a)
        ( b) ＝
      min-Decidable-Total-Order X a b
    max-opposite-Decidable-Total-Order =
      ap pr1
        ( all-elements-equal-has-greatest-binary-lower-bound-Poset
          ( poset-Decidable-Total-Order X)
          ( a)
          ( b)
          ( has-least-binary-upper-bound-Decidable-Total-Order
            ( opposite-Decidable-Total-Order X)
            ( a)
            ( b))
          ( has-greatest-binary-lower-bound-Decidable-Total-Order X a b))
```
