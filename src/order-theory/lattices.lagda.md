# Lattices

```agda
module order-theory.lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.meet-semilattices
open import order-theory.posets
```

</details>

## Idea

A lattice is a poset in which every pair of elements has a meet (a greatest lower bound) and a join (a least upper bound)

## Definitions

### Order theoretic lattices

```agda
is-lattice-poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-lattice-poset-Prop P =
  prod-Prop
    ( is-meet-semilattice-poset-Prop P)
    ( is-join-semilattice-poset-Prop P)

is-lattice-Poset : {l1 l2 : Level} → Poset l1 l2 → UU (l1 ⊔ l2)
is-lattice-Poset P = type-Prop (is-lattice-poset-Prop P)

is-prop-is-lattice-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) → is-prop (is-lattice-Poset P)
is-prop-is-lattice-Poset P = is-prop-type-Prop (is-lattice-poset-Prop P)

Lattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Lattice l1 l2 = Σ (Poset l1 l2) is-lattice-Poset

module _
  {l1 l2 : Level} (A : Lattice l1 l2)
  where

  poset-Lattice : Poset l1 l2
  poset-Lattice = pr1 A

  element-Lattice : UU l1
  element-Lattice = element-Poset poset-Lattice

  leq-lattice-Prop : (x y : element-Lattice) → Prop l2
  leq-lattice-Prop = leq-poset-Prop poset-Lattice

  leq-Lattice : (x y : element-Lattice) → UU l2
  leq-Lattice = leq-Poset poset-Lattice

  is-prop-leq-Lattice : (x y : element-Lattice) → is-prop (leq-Lattice x y)
  is-prop-leq-Lattice = is-prop-leq-Poset poset-Lattice

  refl-leq-Lattice : (x : element-Lattice) → leq-Lattice x x
  refl-leq-Lattice = refl-leq-Poset poset-Lattice

  antisymmetric-leq-Lattice :
    (x y : element-Lattice) → leq-Lattice x y → leq-Lattice y x → Id x y
  antisymmetric-leq-Lattice = antisymmetric-leq-Poset poset-Lattice

  transitive-leq-Lattice :
    (x y z : element-Lattice) →
    leq-Lattice y z → leq-Lattice x y → leq-Lattice x z
  transitive-leq-Lattice = transitive-leq-Poset poset-Lattice

  is-set-element-Lattice : is-set element-Lattice
  is-set-element-Lattice = is-set-element-Poset poset-Lattice

  element-lattice-Set : Set l1
  element-lattice-Set = element-poset-Set poset-Lattice

  is-lattice-poset-Lattice : is-lattice-Poset poset-Lattice
  is-lattice-poset-Lattice = pr2 A

  is-meet-semilattice-Lattice : is-meet-semilattice-Poset poset-Lattice
  is-meet-semilattice-Lattice = pr1 is-lattice-poset-Lattice

  meet-semilattice-Lattice : Meet-Semilattice l1 l2
  pr1 meet-semilattice-Lattice = poset-Lattice
  pr2 meet-semilattice-Lattice = is-meet-semilattice-Lattice

  meet-Lattice : (x y : element-Lattice) → element-Lattice
  meet-Lattice = meet-Meet-Semilattice meet-semilattice-Lattice

  is-join-semilattice-Lattice : is-join-semilattice-Poset poset-Lattice
  is-join-semilattice-Lattice = pr2 is-lattice-poset-Lattice

  join-semilattice-Lattice : Join-Semilattice l1 l2
  pr1 join-semilattice-Lattice = poset-Lattice
  pr2 join-semilattice-Lattice = is-join-semilattice-Lattice

  join-Lattice : (x y : element-Lattice) → element-Lattice
  join-Lattice = join-Join-Semilattice join-semilattice-Lattice
```
