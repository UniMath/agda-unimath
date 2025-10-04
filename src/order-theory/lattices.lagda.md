# Lattices

```agda
module order-theory.lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
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
  {l1 l2 : Level} (A : Lattice l1 l2)
  where

  poset-Lattice : Poset l1 l2
  poset-Lattice = pr1 A

  type-Lattice : UU l1
  type-Lattice = type-Poset poset-Lattice

  leq-lattice-Prop : (x y : type-Lattice) → Prop l2
  leq-lattice-Prop = leq-prop-Poset poset-Lattice

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
  is-lattice-Lattice = pr2 A

  is-meet-semilattice-Lattice : is-meet-semilattice-Poset poset-Lattice
  is-meet-semilattice-Lattice = pr1 is-lattice-Lattice

  meet-semilattice-Lattice : Meet-Semilattice l1
  meet-semilattice-Lattice =
    meet-semilattice-Order-Theoretic-Meet-Semilattice
      ( poset-Lattice ,
        is-meet-semilattice-Lattice)

  meet-Lattice : (x y : type-Lattice) → type-Lattice
  meet-Lattice x y = pr1 (is-meet-semilattice-Lattice x y)

  is-join-semilattice-Lattice : is-join-semilattice-Poset poset-Lattice
  is-join-semilattice-Lattice = pr2 is-lattice-Lattice

  join-semilattice-Lattice : Join-Semilattice l1
  join-semilattice-Lattice =
    join-semilattice-Order-Theoretic-Join-Semilattice
      ( poset-Lattice ,
        is-join-semilattice-Lattice)

  join-Lattice : (x y : type-Lattice) → type-Lattice
  join-Lattice x y = pr1 (is-join-semilattice-Lattice x y)
```
