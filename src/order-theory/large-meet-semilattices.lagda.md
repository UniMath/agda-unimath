# Large meet-semilattices

```agda
module order-theory.large-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.large-semigroups
```

</details>

## Idea

A **large meet-semilattice** is a
[large semigroup](group-theory.large-semigroups.md) which is commutative and
idempotent.

## Definition

```agda
record Large-Meet-Semilattice (α : Level → Level) : UUω where
  constructor
    make-Large-Meet-Semilattice
  field
    large-semigroup-Large-Meet-Semilattice :
      Large-Semigroup α
    commutative-meet-Large-Meet-Semilattice :
      {l1 l2 : Level}
      (x : type-Large-Semigroup large-semigroup-Large-Meet-Semilattice l1)
      (y : type-Large-Semigroup large-semigroup-Large-Meet-Semilattice l2) →
      mul-Large-Semigroup large-semigroup-Large-Meet-Semilattice x y ＝
      mul-Large-Semigroup large-semigroup-Large-Meet-Semilattice y x
    idempotent-meet-Large-Meet-Semilattice :
      {l1 : Level}
      (x : type-Large-Semigroup large-semigroup-Large-Meet-Semilattice l1) →
      mul-Large-Semigroup large-semigroup-Large-Meet-Semilattice x x ＝ x

open Large-Meet-Semilattice public

module _
  {α : Level → Level} (L : Large-Meet-Semilattice α)
  where

  type-Large-Meet-Semilattice : (l : Level) → UU (α l)
  type-Large-Meet-Semilattice =
    type-Large-Semigroup (large-semigroup-Large-Meet-Semilattice L)

  set-Large-Meet-Semilattice : (l : Level) → Set (α l)
  set-Large-Meet-Semilattice =
    set-Large-Semigroup (large-semigroup-Large-Meet-Semilattice L)

  is-set-type-Large-Meet-Semilattice :
    {l : Level} → is-set (type-Large-Meet-Semilattice l)
  is-set-type-Large-Meet-Semilattice =
    is-set-type-Large-Semigroup (large-semigroup-Large-Meet-Semilattice L)

  meet-Large-Meet-Semilattice :
    {l1 l2 : Level} →
    type-Large-Meet-Semilattice l1 → type-Large-Meet-Semilattice l2 →
    type-Large-Meet-Semilattice (l1 ⊔ l2)
  meet-Large-Meet-Semilattice =
    mul-Large-Semigroup (large-semigroup-Large-Meet-Semilattice L)

  associative-meet-Large-Meet-Semilattice :
    {l1 l2 l3 : Level} →
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2)
    (z : type-Large-Meet-Semilattice l3) →
    meet-Large-Meet-Semilattice (meet-Large-Meet-Semilattice x y) z ＝
    meet-Large-Meet-Semilattice x (meet-Large-Meet-Semilattice y z)
  associative-meet-Large-Meet-Semilattice =
    associative-mul-Large-Semigroup (large-semigroup-Large-Meet-Semilattice L)
```
