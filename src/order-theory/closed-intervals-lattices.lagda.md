# Closed intervals in lattices

```agda
module order-theory.closed-intervals-lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
open import order-theory.lattices
```

</details>

## Idea

A
{{#concept "closed interval" disambiguation="in a lattice" Agda=closed-interval-Lattice}}
in a [lattice](order-theory.lattices.md) `L` is a
[subtype](foundation.subtypes.md) of `L` with elements `x` and `y` with `x ≤ y`
such that the subtype contains every element `z` such that `x ≤ z ∧ z ≤ y`.
Note, in particular, that we thus consider closed intervals to be inhabited by
convention.

Equivalently, a closed interval is a total order is a
[closed interval](order-theory.closed-intervals-posets.md) in the underlying
[poset](order-theory.posets.md).

## Definition

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  closed-interval-Lattice : UU (l1 ⊔ l2)
  closed-interval-Lattice =
    closed-interval-Poset (poset-Lattice L)

  lower-bound-closed-interval-Lattice :
    closed-interval-Lattice → type-Lattice L
  lower-bound-closed-interval-Lattice ((x , _) , _) = x

  upper-bound-closed-interval-Lattice :
    closed-interval-Lattice → type-Lattice L
  upper-bound-closed-interval-Lattice ((_ , y) , _) = y

  subtype-closed-interval-Lattice :
    closed-interval-Lattice → subtype l2 (type-Lattice L)
  subtype-closed-interval-Lattice =
    subtype-closed-interval-Poset (poset-Lattice L)

  type-closed-interval-Lattice :
    closed-interval-Lattice → UU (l1 ⊔ l2)
  type-closed-interval-Lattice =
    type-closed-interval-Poset (poset-Lattice L)

  is-in-closed-interval-Lattice :
    closed-interval-Lattice → type-Lattice L → UU l2
  is-in-closed-interval-Lattice =
    is-in-closed-interval-Poset (poset-Lattice L)
```

## Properties

### The endpoints of a closed interval are in the interval

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    lower-bound-is-in-closed-interval-Lattice :
      ([a,b] : closed-interval-Lattice L) →
      is-in-closed-interval-Lattice L [a,b]
        ( lower-bound-closed-interval-Lattice L [a,b])
    lower-bound-is-in-closed-interval-Lattice =
      lower-bound-is-in-closed-interval-Poset (poset-Lattice L)

    upper-bound-is-in-closed-interval-Lattice :
      ([a,b] : closed-interval-Lattice L) →
      is-in-closed-interval-Lattice L [a,b]
        ( upper-bound-closed-interval-Lattice L [a,b])
    upper-bound-is-in-closed-interval-Lattice =
      upper-bound-is-in-closed-interval-Poset (poset-Lattice L)
```

### Closed intervals are inhabited

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  ([x,y] : closed-interval-Lattice L)
  where

  abstract
    is-inhabited-closed-interval-Lattice :
      is-inhabited-subtype
        ( subtype-closed-interval-Lattice L [x,y])
    is-inhabited-closed-interval-Lattice =
      is-inhabited-closed-interval-Poset (poset-Lattice L) [x,y]
```

### Characterization of equality

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    eq-closed-interval-Lattice :
      ( [a,b] [c,d] : closed-interval-Lattice L) →
      ( lower-bound-closed-interval-Lattice L [a,b] ＝
        lower-bound-closed-interval-Lattice L [c,d]) →
      ( upper-bound-closed-interval-Lattice L [a,b] ＝
        upper-bound-closed-interval-Lattice L [c,d]) →
      [a,b] ＝ [c,d]
    eq-closed-interval-Lattice =
      eq-closed-interval-Poset (poset-Lattice L)

  set-closed-interval-Lattice : Set (l1 ⊔ l2)
  set-closed-interval-Lattice =
    set-closed-interval-Poset (poset-Lattice L)
```

### The map from closed intervals to subtypes is injective

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    is-injective-subtype-closed-interval-Lattice :
      is-injective (subtype-closed-interval-Lattice L)
    is-injective-subtype-closed-interval-Lattice =
      is-injective-subtype-closed-interval-Poset (poset-Lattice L)
```
