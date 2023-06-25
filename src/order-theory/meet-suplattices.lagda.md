# Meet-suplattices

```agda
module order-theory.meet-suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

An **`l`-meet-suplattice** is a meet-semilattice `L` which has least upper
bounds for all families of elements `x : I → L` indexed by a type `I : UU l`.

Note that meet-suplattices are not required to satisfy a distributive law. Such
meet-suplattices are called [frames](order-theory.frames.md).

## Definitions

### The predicate on meet-semilattices of being a meet-suplattice

```agda
module _
  {l1 : Level} (l2 : Level) (X : Meet-Semilattice l1)
  where

  is-meet-suplattice-Meet-Semilattice-Prop : Prop (l1 ⊔ lsuc l2)
  is-meet-suplattice-Meet-Semilattice-Prop =
    is-suplattice-Poset-Prop l2 (poset-Meet-Semilattice X)

  is-meet-suplattice-Meet-Semilattice : UU (l1 ⊔ lsuc l2)
  is-meet-suplattice-Meet-Semilattice =
    type-Prop is-meet-suplattice-Meet-Semilattice-Prop

  is-prop-is-meet-suplattice-Meet-Semilattice :
    is-prop is-meet-suplattice-Meet-Semilattice
  is-prop-is-meet-suplattice-Meet-Semilattice =
    is-prop-type-Prop is-meet-suplattice-Meet-Semilattice-Prop
```

### Meet-suplattices

```agda
Meet-Suplattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Meet-Suplattice l1 l2 =
  Σ (Meet-Semilattice l1) (is-meet-suplattice-Meet-Semilattice l2)

module _
  {l1 l2 : Level} (A : Meet-Suplattice l1 l2)
  where

  meet-semilattice-Meet-Suplattice : Meet-Semilattice l1
  meet-semilattice-Meet-Suplattice = pr1 A

  poset-Meet-Suplattice : Poset l1 l1
  poset-Meet-Suplattice =
    poset-Meet-Semilattice meet-semilattice-Meet-Suplattice

  type-Meet-Suplattice : UU l1
  type-Meet-Suplattice =
    type-Poset poset-Meet-Suplattice

  leq-meet-suplattice-Prop : (x y : type-Meet-Suplattice) → Prop l1
  leq-meet-suplattice-Prop = leq-Poset-Prop poset-Meet-Suplattice

  leq-Meet-Suplattice : (x y : type-Meet-Suplattice) → UU l1
  leq-Meet-Suplattice = leq-Poset poset-Meet-Suplattice

  is-prop-leq-Meet-Suplattice :
    (x y : type-Meet-Suplattice) → is-prop (leq-Meet-Suplattice x y)
  is-prop-leq-Meet-Suplattice = is-prop-leq-Poset poset-Meet-Suplattice

  refl-leq-Meet-Suplattice : is-reflexive leq-Meet-Suplattice
  refl-leq-Meet-Suplattice = refl-leq-Poset poset-Meet-Suplattice

  antisymmetric-leq-Meet-Suplattice : is-antisymmetric leq-Meet-Suplattice
  antisymmetric-leq-Meet-Suplattice =
    antisymmetric-leq-Poset poset-Meet-Suplattice

  transitive-leq-Meet-Suplattice : is-transitive leq-Meet-Suplattice
  transitive-leq-Meet-Suplattice = transitive-leq-Poset poset-Meet-Suplattice

  is-set-type-Meet-Suplattice : is-set type-Meet-Suplattice
  is-set-type-Meet-Suplattice = is-set-type-Poset poset-Meet-Suplattice

  set-Meet-Suplattice : Set l1
  set-Meet-Suplattice = set-Poset poset-Meet-Suplattice

  is-suplattice-Meet-Suplattice :
    is-suplattice-Poset l2 poset-Meet-Suplattice
  is-suplattice-Meet-Suplattice = pr2 A

  suplattice-Meet-Suplattice : Suplattice l1 l1 l2
  suplattice-Meet-Suplattice =
    ( poset-Meet-Suplattice , is-suplattice-Meet-Suplattice)

  meet-Meet-Suplattice :
    (x y : type-Meet-Suplattice) →
    type-Meet-Suplattice
  meet-Meet-Suplattice =
    meet-Meet-Semilattice meet-semilattice-Meet-Suplattice

  sup-Meet-Suplattice :
    {I : UU l2} → (I → type-Meet-Suplattice) →
    type-Meet-Suplattice
  sup-Meet-Suplattice {I} f = pr1 (is-suplattice-Meet-Suplattice I f)
```
