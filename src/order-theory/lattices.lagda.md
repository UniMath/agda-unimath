# Lattices

```agda
module order-theory.lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.meet-semilattices
open import order-theory.posets
```

</details>

## Idea

A {{#concept "lattice" WDID=Q595364 WD="lattice" Agda=Lattice}} is a
[poset](order-theory.posets.md) in which every pair of elements has a meet (a
[greatest lower bound](order-theory.greatest-lower-bounds-posets.md)) and a join
(a [least upper bound](order-theory.least-upper-bounds-posets.md)).

Note that we don't require that meets distribute over joins. Such lattices are
called [distributive lattices](order-theory.distributive-lattices.md).

## Definitions

### Order theoretic lattices

```agda
is-lattice-Poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-lattice-Poset-Prop P =
  product-Prop
    ( is-meet-semilattice-Poset-Prop P)
    ( is-join-semilattice-Poset-Prop P)

is-lattice-Poset : {l1 l2 : Level} → Poset l1 l2 → UU (l1 ⊔ l2)
is-lattice-Poset P = type-Prop (is-lattice-Poset-Prop P)

is-prop-is-lattice-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) → is-prop (is-lattice-Poset P)
is-prop-is-lattice-Poset P = is-prop-type-Prop (is-lattice-Poset-Prop P)

Lattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Lattice l1 l2 = Σ (Poset l1 l2) is-lattice-Poset

module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  poset-Lattice : Poset l1 l2
  poset-Lattice = pr1 L

  type-Lattice : UU l1
  type-Lattice = type-Poset poset-Lattice

  leq-prop-Lattice : (x y : type-Lattice) → Prop l2
  leq-prop-Lattice = leq-prop-Poset poset-Lattice

  leq-Lattice : (x y : type-Lattice) → UU l2
  leq-Lattice = leq-Poset poset-Lattice

  is-prop-leq-Lattice : (x y : type-Lattice) → is-prop (leq-Lattice x y)
  is-prop-leq-Lattice = is-prop-leq-Poset poset-Lattice

  refl-leq-Lattice : is-reflexive leq-Lattice
  refl-leq-Lattice = refl-leq-Poset poset-Lattice

  antisymmetric-leq-Lattice : is-antisymmetric leq-Lattice
  antisymmetric-leq-Lattice = antisymmetric-leq-Poset poset-Lattice

  transitive-leq-Lattice : is-transitive leq-Lattice
  transitive-leq-Lattice = transitive-leq-Poset poset-Lattice

  is-set-type-Lattice : is-set type-Lattice
  is-set-type-Lattice = is-set-type-Poset poset-Lattice

  set-Lattice : Set l1
  set-Lattice = set-Poset poset-Lattice

  is-lattice-Lattice : is-lattice-Poset poset-Lattice
  is-lattice-Lattice = pr2 L

  is-meet-semilattice-Lattice : is-meet-semilattice-Poset poset-Lattice
  is-meet-semilattice-Lattice = pr1 is-lattice-Lattice

  order-theoretic-meet-semilattice-Lattice :
    Order-Theoretic-Meet-Semilattice l1 l2
  order-theoretic-meet-semilattice-Lattice =
    ( poset-Lattice , is-meet-semilattice-Lattice)

  meet-semilattice-Lattice : Meet-Semilattice l1
  meet-semilattice-Lattice =
    meet-semilattice-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Lattice)

  meet-Lattice : (x y : type-Lattice) → type-Lattice
  meet-Lattice x y = pr1 (is-meet-semilattice-Lattice x y)

  is-join-semilattice-Lattice : is-join-semilattice-Poset poset-Lattice
  is-join-semilattice-Lattice = pr2 is-lattice-Lattice

  order-theoretic-join-semilattice-Lattice :
    Order-Theoretic-Join-Semilattice l1 l2
  order-theoretic-join-semilattice-Lattice =
    ( poset-Lattice , is-join-semilattice-Lattice)

  join-semilattice-Lattice : Join-Semilattice l1
  join-semilattice-Lattice =
    join-semilattice-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Lattice)

  join-Lattice : (x y : type-Lattice) → type-Lattice
  join-Lattice x y = pr1 (is-join-semilattice-Lattice x y)
```

## Properties

### If `a ≤ b` and `c ≤ d`, then the meet of `a` and `c` is less than or equal to the meet of `c` and `d`

```agda
module _
  {l1 l2 : Level}
  (L : Lattice l1 l2)
  where

  abstract
    meet-leq-leq-Lattice :
      (a b c d : type-Lattice L) →
      leq-Lattice L a b → leq-Lattice L c d →
      leq-Lattice
        ( L)
        ( meet-Lattice L a c)
        ( meet-Lattice L b d)
    meet-leq-leq-Lattice =
      meet-leq-leq-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)
```

### If `a ≤ b` and `a ≤ c`, then `a` is less than or equal to the meet of `b` and `c`

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    leq-meet-leq-both-Lattice :
      (a b c : type-Lattice L) →
      leq-Lattice L a b → leq-Lattice L a c →
      leq-Lattice L a (meet-Lattice L b c)
    leq-meet-leq-both-Lattice =
      leq-meet-leq-both-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)
```

### If `a ≤ c` and `b ≤ c`, then the join of `a` and `b` is less than or equal to `c`

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    leq-join-leq-both-Lattice :
      (a b c : type-Lattice L) →
      leq-Lattice L a c → leq-Lattice L b c →
      leq-Lattice L (join-Lattice L a b) c
    leq-join-leq-both-Lattice =
      leq-join-leq-both-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Lattice L)
```

### The meet is a lower bound

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    leq-left-meet-Lattice :
      (a b : type-Lattice L) → leq-Lattice L (meet-Lattice L a b) a
    leq-left-meet-Lattice =
      leq-left-meet-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)

    leq-right-meet-Lattice :
      (a b : type-Lattice L) → leq-Lattice L (meet-Lattice L a b) b
    leq-right-meet-Lattice =
      leq-right-meet-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)
```

### The join is an upper bound

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    leq-left-join-Lattice :
      (a b : type-Lattice L) → leq-Lattice L a (join-Lattice L a b)
    leq-left-join-Lattice =
      leq-left-join-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Lattice L)

    leq-right-join-Lattice :
      (a b : type-Lattice L) → leq-Lattice L b (join-Lattice L a b)
    leq-right-join-Lattice =
      leq-right-join-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Lattice L)
```

### If `x` is less than or equal to `y`, the join of `x` and `y` is `y`

```agda
module _
  {l1 l2 : Level}
  (L : Lattice l1 l2)
  where

  abstract
    left-leq-right-join-Lattice :
      (x y : type-Lattice L) → leq-Lattice L x y → join-Lattice L x y ＝ y
    left-leq-right-join-Lattice =
      left-leq-right-join-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Lattice L)
```

### If `y` is less than or equal to `x`, the join of `x` and `y` is `x`

```agda
module _
  {l1 l2 : Level}
  (L : Lattice l1 l2)
  where

  abstract
    right-leq-left-join-Lattice :
      (x y : type-Lattice L) → leq-Lattice L y x → join-Lattice L x y ＝ x
    right-leq-left-join-Lattice =
      right-leq-left-join-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Lattice L)
```

### If `x` is less than or equal to `y`, the meet of `x` and `y` is `x`

```agda
module _
  {l1 l2 : Level}
  (L : Lattice l1 l2)
  where

  abstract
    left-leq-right-meet-Lattice :
      (x y : type-Lattice L) → leq-Lattice L x y → meet-Lattice L x y ＝ x
    left-leq-right-meet-Lattice =
      left-leq-right-meet-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)
```

### If `y` is less than or equal to `x`, the meet of `x` and `y` is `y`

```agda
module _
  {l1 l2 : Level}
  (L : Lattice l1 l2)
  where

  abstract
    right-leq-left-meet-Lattice :
      (x y : type-Lattice L) → leq-Lattice L y x → meet-Lattice L x y ＝ y
    right-leq-left-meet-Lattice =
      right-leq-left-meet-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Lattice L)
```
