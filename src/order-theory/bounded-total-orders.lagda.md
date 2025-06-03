# Bounded total orders

```agda
module order-theory.bounded-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.posets
open import order-theory.top-elements-posets
open import order-theory.total-orders
```

</details>

## Idea

A bounded total order is a [total order](order-theory.total-orders.md) equipped
with a top and bottom element.

## Definitions

### The predicate of being a bounded total order

```agda
module _
  {l1 l2 : Level} (L : Total-Order l1 l2)
  where

  is-bounded-Total-Order : UU (l1 ⊔ l2)
  is-bounded-Total-Order =
    has-top-element-Poset (poset-Total-Order L) ×
    has-bottom-element-Poset (poset-Total-Order L)
```

### Bounded total orders

```agda
Bounded-Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Bounded-Total-Order l1 l2 =
  Σ (Total-Order l1 l2) is-bounded-Total-Order

module _
  {l1 l2 : Level} (L : Bounded-Total-Order l1 l2)
  where

  total-order-Bounded-Total-Order : Total-Order l1 l2
  total-order-Bounded-Total-Order = pr1 L

  poset-Bounded-Total-Order : Poset l1 l2
  poset-Bounded-Total-Order =
    poset-Total-Order total-order-Bounded-Total-Order

  type-Bounded-Total-Order : UU l1
  type-Bounded-Total-Order =
    type-Total-Order total-order-Bounded-Total-Order

  leq-prop-Bounded-Total-Order :
    (x y : type-Bounded-Total-Order) → Prop l2
  leq-prop-Bounded-Total-Order =
    leq-prop-Poset poset-Bounded-Total-Order

  leq-Bounded-Total-Order :
    (x y : type-Bounded-Total-Order) → UU l2
  leq-Bounded-Total-Order =
    leq-Poset poset-Bounded-Total-Order

  is-prop-leq-Bounded-Total-Order :
    (x y : type-Bounded-Total-Order) → is-prop (leq-Bounded-Total-Order x y)
  is-prop-leq-Bounded-Total-Order =
    is-prop-leq-Poset poset-Bounded-Total-Order

  refl-leq-Bounded-Total-Order :
    is-reflexive leq-Bounded-Total-Order
  refl-leq-Bounded-Total-Order =
    refl-leq-Poset poset-Bounded-Total-Order

  transitive-leq-Bounded-Total-Order :
    is-transitive leq-Bounded-Total-Order
  transitive-leq-Bounded-Total-Order =
    transitive-leq-Poset poset-Bounded-Total-Order

  antisymmetric-leq-Bounded-Total-Order :
    is-antisymmetric leq-Bounded-Total-Order
  antisymmetric-leq-Bounded-Total-Order =
    antisymmetric-leq-Poset poset-Bounded-Total-Order

  has-top-element-Bounded-Total-Order :
    has-top-element-Poset poset-Bounded-Total-Order
  has-top-element-Bounded-Total-Order =
    pr1 (pr2 L)

  top-Bounded-Total-Order :
    type-Bounded-Total-Order
  top-Bounded-Total-Order =
    pr1 has-top-element-Bounded-Total-Order

  is-top-element-top-Bounded-Total-Order :
    is-top-element-Poset poset-Bounded-Total-Order top-Bounded-Total-Order
  is-top-element-top-Bounded-Total-Order =
    pr2 has-top-element-Bounded-Total-Order

  has-bottom-element-Bounded-Total-Order :
    has-bottom-element-Poset poset-Bounded-Total-Order
  has-bottom-element-Bounded-Total-Order =
    pr2 (pr2 L)

  bottom-Bounded-Total-Order :
    type-Bounded-Total-Order
  bottom-Bounded-Total-Order =
    pr1 has-bottom-element-Bounded-Total-Order

  is-bottom-element-bottom-Bounded-Total-Order :
    is-bottom-element-Poset poset-Bounded-Total-Order bottom-Bounded-Total-Order
  is-bottom-element-bottom-Bounded-Total-Order =
    pr2 has-bottom-element-Bounded-Total-Order
```
