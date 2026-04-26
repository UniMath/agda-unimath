# The poset of closed intervals in lattices

```agda
module order-theory.poset-closed-intervals-lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-lattices
open import order-theory.lattices
open import order-theory.poset-closed-intervals-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

In a [lattice](order-theory.lattices.md) `L`, the type of
[closed intervals](order-theory.closed-intervals-lattices.md) in `L` itself
forms a [poset](order-theory.posets.md), with inequality defined by containment
of the corresponding subtypes. Equivalently, `[a,b] ≤ [c,d]` if `c ≤ a` and
`b ≤ d`.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  leq-prop-closed-interval-Lattice :
    Relation-Prop l2 (closed-interval-Lattice L)
  leq-prop-closed-interval-Lattice =
    leq-prop-closed-interval-Poset (poset-Lattice L)

  leq-closed-interval-Lattice : Relation l2 (closed-interval-Lattice L)
  leq-closed-interval-Lattice =
    leq-closed-interval-Poset (poset-Lattice L)
```

## Properties

### Containment is a preorder

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  refl-leq-closed-interval-Lattice :
    is-reflexive (leq-closed-interval-Lattice L)
  refl-leq-closed-interval-Lattice =
    refl-leq-closed-interval-Poset (poset-Lattice L)

  transitive-leq-closed-interval-Lattice :
    is-transitive (leq-closed-interval-Lattice L)
  transitive-leq-closed-interval-Lattice =
    transitive-leq-closed-interval-Poset (poset-Lattice L)

  is-preorder-leq-closed-interval-Lattice :
    is-preorder-Relation-Prop (leq-prop-closed-interval-Lattice L)
  is-preorder-leq-closed-interval-Lattice =
    is-preorder-leq-closed-interval-Poset (poset-Lattice L)
```

### Containment is a poset

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  antisymmetric-leq-closed-interval-Lattice :
    is-antisymmetric (leq-closed-interval-Lattice L)
  antisymmetric-leq-closed-interval-Lattice =
    antisymmetric-leq-closed-interval-Poset (poset-Lattice L)

  poset-closed-interval-Lattice : Poset (l1 ⊔ l2) l2
  poset-closed-interval-Lattice =
    poset-closed-interval-Poset (poset-Lattice L)
```

### Containment of closed intervals is equivalent to containment of subtypes

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  leq-subtype-leq-closed-interval-Lattice :
    ([a,b] [c,d] : closed-interval-Lattice L) →
    leq-closed-interval-Lattice L [a,b] [c,d] →
    ( subtype-closed-interval-Lattice L [a,b] ⊆
      subtype-closed-interval-Lattice L [c,d])
  leq-subtype-leq-closed-interval-Lattice =
    leq-subtype-leq-closed-interval-Poset (poset-Lattice L)

  leq-closed-interval-leq-subtype-Lattice :
    ([a,b] [c,d] : closed-interval-Lattice L) →
    ( subtype-closed-interval-Lattice L [a,b] ⊆
      subtype-closed-interval-Lattice L [c,d]) →
    leq-closed-interval-Lattice L [a,b] [c,d]
  leq-closed-interval-leq-subtype-Lattice =
    leq-closed-interval-leq-subtype-Poset (poset-Lattice L)

  leq-subtype-iff-leq-closed-interval-Lattice :
    ([a,b] [c,d] : closed-interval-Lattice L) →
    ( leq-closed-interval-Lattice L [a,b] [c,d] ↔
      ( subtype-closed-interval-Lattice L [a,b] ⊆
        subtype-closed-interval-Lattice L [c,d]))
  leq-subtype-iff-leq-closed-interval-Lattice =
    leq-subtype-iff-leq-closed-interval-Poset (poset-Lattice L)
```
