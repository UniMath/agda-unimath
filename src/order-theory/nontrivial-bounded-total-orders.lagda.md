# Nontrivial bounded total orders

```agda
module order-theory.nontrivial-bounded-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.bounded-total-orders
open import order-theory.posets
open import order-theory.top-elements-posets
open import order-theory.total-orders
```

</details>

## Idea

A
{{#concept "nontrivial bounded total order" Agda=Nontrivial-Bounded-Total-Order}}
is a [bounded total order](order-theory.bounded-total-orders.md) whose
[top](order-theory.top-elements-posets.md) and
[bottom](order-theory.bottom-elements-posets.md) elements are
[distinct](foundation.negated-equality.md).

## Definitions

### The predicate of being a nontrivial bounded total order

```agda
module _
  {l1 l2 : Level} (L : Bounded-Total-Order l1 l2)
  where

  is-nontrivial-Bounded-Total-Order : UU l1
  is-nontrivial-Bounded-Total-Order =
    top-Bounded-Total-Order L ≠ bottom-Bounded-Total-Order L
```

### Nontrivial bounded total orders

```agda
Nontrivial-Bounded-Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Nontrivial-Bounded-Total-Order l1 l2 =
  Σ (Bounded-Total-Order l1 l2) is-nontrivial-Bounded-Total-Order

module _
  {l1 l2 : Level} (L : Nontrivial-Bounded-Total-Order l1 l2)
  where

  bounded-total-order-Nontrivial-Bounded-Total-Order : Bounded-Total-Order l1 l2
  bounded-total-order-Nontrivial-Bounded-Total-Order = pr1 L

  total-order-Nontrivial-Bounded-Total-Order : Total-Order l1 l2
  total-order-Nontrivial-Bounded-Total-Order =
    total-order-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  poset-Nontrivial-Bounded-Total-Order : Poset l1 l2
  poset-Nontrivial-Bounded-Total-Order =
    poset-Total-Order total-order-Nontrivial-Bounded-Total-Order

  type-Nontrivial-Bounded-Total-Order : UU l1
  type-Nontrivial-Bounded-Total-Order =
    type-Total-Order total-order-Nontrivial-Bounded-Total-Order

  leq-prop-Nontrivial-Bounded-Total-Order :
    (x y : type-Nontrivial-Bounded-Total-Order) → Prop l2
  leq-prop-Nontrivial-Bounded-Total-Order =
    leq-prop-Poset poset-Nontrivial-Bounded-Total-Order

  leq-Nontrivial-Bounded-Total-Order :
    (x y : type-Nontrivial-Bounded-Total-Order) → UU l2
  leq-Nontrivial-Bounded-Total-Order =
    leq-Poset poset-Nontrivial-Bounded-Total-Order

  is-prop-leq-Nontrivial-Bounded-Total-Order :
    (x y : type-Nontrivial-Bounded-Total-Order) → is-prop (leq-Nontrivial-Bounded-Total-Order x y)
  is-prop-leq-Nontrivial-Bounded-Total-Order =
    is-prop-leq-Poset poset-Nontrivial-Bounded-Total-Order

  refl-leq-Nontrivial-Bounded-Total-Order :
    is-reflexive leq-Nontrivial-Bounded-Total-Order
  refl-leq-Nontrivial-Bounded-Total-Order =
    refl-leq-Poset poset-Nontrivial-Bounded-Total-Order

  transitive-leq-Nontrivial-Bounded-Total-Order :
    is-transitive leq-Nontrivial-Bounded-Total-Order
  transitive-leq-Nontrivial-Bounded-Total-Order =
    transitive-leq-Poset poset-Nontrivial-Bounded-Total-Order

  antisymmetric-leq-Nontrivial-Bounded-Total-Order :
    is-antisymmetric leq-Nontrivial-Bounded-Total-Order
  antisymmetric-leq-Nontrivial-Bounded-Total-Order =
    antisymmetric-leq-Poset poset-Nontrivial-Bounded-Total-Order

  has-top-element-Nontrivial-Bounded-Total-Order :
    has-top-element-Poset poset-Nontrivial-Bounded-Total-Order
  has-top-element-Nontrivial-Bounded-Total-Order =
    has-top-element-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  top-Nontrivial-Bounded-Total-Order :
    type-Nontrivial-Bounded-Total-Order
  top-Nontrivial-Bounded-Total-Order =
    top-Bounded-Total-Order bounded-total-order-Nontrivial-Bounded-Total-Order

  is-top-element-top-Nontrivial-Bounded-Total-Order :
    is-top-element-Poset
      poset-Nontrivial-Bounded-Total-Order
      top-Nontrivial-Bounded-Total-Order
  is-top-element-top-Nontrivial-Bounded-Total-Order =
    is-top-element-top-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  has-bottom-element-Nontrivial-Bounded-Total-Order :
    has-bottom-element-Poset poset-Nontrivial-Bounded-Total-Order
  has-bottom-element-Nontrivial-Bounded-Total-Order =
    has-bottom-element-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  bottom-Nontrivial-Bounded-Total-Order :
    type-Nontrivial-Bounded-Total-Order
  bottom-Nontrivial-Bounded-Total-Order =
    bottom-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  is-bottom-element-bottom-Nontrivial-Bounded-Total-Order :
    is-bottom-element-Poset
      poset-Nontrivial-Bounded-Total-Order
      bottom-Nontrivial-Bounded-Total-Order
  is-bottom-element-bottom-Nontrivial-Bounded-Total-Order =
    is-bottom-element-bottom-Bounded-Total-Order
      bounded-total-order-Nontrivial-Bounded-Total-Order

  is-nontrivial-Nontrivial-Bounded-Total-Order :
    top-Nontrivial-Bounded-Total-Order ≠ bottom-Nontrivial-Bounded-Total-Order
  is-nontrivial-Nontrivial-Bounded-Total-Order = pr2 L
```
