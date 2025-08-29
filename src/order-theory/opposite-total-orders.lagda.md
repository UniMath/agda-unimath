# Opposite total orders

```agda
module order-theory.opposite-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.opposite-posets
open import order-theory.posets
open import order-theory.total-orders
```

</details>

## Idea

Let `X` be a [total order](order-theory.total-orders.md). Its
{{#concept "opposite" Disambiguation="total order" Agda=opposite-Total-Order}}
`Xᵒᵖ` is given by reversing the relation.

## Definition

### The opposite total order

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  poset-opposite-Total-Order : Poset l1 l2
  poset-opposite-Total-Order = opposite-Poset (poset-Total-Order X)

  abstract
    is-total-poset-opposite-Total-Order :
      is-total-Poset poset-opposite-Total-Order
    is-total-poset-opposite-Total-Order x y =
      elim-disjunction
        ( incident-Poset-Prop poset-opposite-Total-Order x y)
        ( inr-disjunction)
        ( inl-disjunction)
        ( is-total-Total-Order X x y)

  opposite-Total-Order : Total-Order l1 l2
  opposite-Total-Order =
    ( poset-opposite-Total-Order ,
      is-total-poset-opposite-Total-Order)
```
