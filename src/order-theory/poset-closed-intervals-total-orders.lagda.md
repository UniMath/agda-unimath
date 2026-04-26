# The poset of closed intervals in total orders

```agda
module order-theory.poset-closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-total-orders
open import order-theory.poset-closed-intervals-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

In a [total order](order-theory.total-orders.md) `T`, the type of
[closed intervals](order-theory.closed-intervals-total-orders.md) in `T` itself
forms a [poset](order-theory.posets.md), with inequality defined by containment
of the corresponding subtypes. Equivalently, `[a,b] ≤ [c,d]` if `c ≤ a` and
`b ≤ d`.

## Definition

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  leq-prop-closed-interval-Total-Order :
    Relation-Prop l2 (closed-interval-Total-Order T)
  leq-prop-closed-interval-Total-Order =
    leq-prop-closed-interval-Poset (poset-Total-Order T)

  leq-closed-interval-Total-Order : Relation l2 (closed-interval-Total-Order T)
  leq-closed-interval-Total-Order =
    leq-closed-interval-Poset (poset-Total-Order T)
```

## Properties

### Containment is a preorder

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  refl-leq-closed-interval-Total-Order :
    is-reflexive (leq-closed-interval-Total-Order T)
  refl-leq-closed-interval-Total-Order =
    refl-leq-closed-interval-Poset (poset-Total-Order T)

  transitive-leq-closed-interval-Total-Order :
    is-transitive (leq-closed-interval-Total-Order T)
  transitive-leq-closed-interval-Total-Order =
    transitive-leq-closed-interval-Poset (poset-Total-Order T)

  is-preorder-leq-closed-interval-Total-Order :
    is-preorder-Relation-Prop (leq-prop-closed-interval-Total-Order T)
  is-preorder-leq-closed-interval-Total-Order =
    is-preorder-leq-closed-interval-Poset (poset-Total-Order T)
```

### Containment is a poset

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  antisymmetric-leq-closed-interval-Total-Order :
    is-antisymmetric (leq-closed-interval-Total-Order T)
  antisymmetric-leq-closed-interval-Total-Order =
    antisymmetric-leq-closed-interval-Poset (poset-Total-Order T)

  poset-closed-interval-Total-Order : Poset (l1 ⊔ l2) l2
  poset-closed-interval-Total-Order =
    poset-closed-interval-Poset (poset-Total-Order T)
```

### Containment of closed intervals is equivalent to containment of subtypes

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  leq-subtype-leq-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    leq-closed-interval-Total-Order T [a,b] [c,d] →
    ( subtype-closed-interval-Total-Order T [a,b] ⊆
      subtype-closed-interval-Total-Order T [c,d])
  leq-subtype-leq-closed-interval-Total-Order =
    leq-subtype-leq-closed-interval-Poset (poset-Total-Order T)

  leq-closed-interval-leq-subtype-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    ( subtype-closed-interval-Total-Order T [a,b] ⊆
      subtype-closed-interval-Total-Order T [c,d]) →
    leq-closed-interval-Total-Order T [a,b] [c,d]
  leq-closed-interval-leq-subtype-Total-Order =
    leq-closed-interval-leq-subtype-Poset (poset-Total-Order T)

  leq-subtype-iff-leq-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    ( leq-closed-interval-Total-Order T [a,b] [c,d] ↔
      ( subtype-closed-interval-Total-Order T [a,b] ⊆
        subtype-closed-interval-Total-Order T [c,d]))
  leq-subtype-iff-leq-closed-interval-Total-Order =
    leq-subtype-iff-leq-closed-interval-Poset (poset-Total-Order T)
```
