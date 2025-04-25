# Finite sequences on commutative rings

```agda
module linear-algebra.finite-sequences-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-on-rings
```

</details>

## Idea

Finite sequences on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` are
[finite sequences](linear-algebra.finite-sequences.md) on the underlying type of
`R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  fin-sequence-Commutative-Ring : ℕ → UU l
  fin-sequence-Commutative-Ring =
    fin-sequence-Ring (ring-Commutative-Ring R)

  head-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence-Commutative-Ring (succ-ℕ n) →
    type-Commutative-Ring R
  head-fin-sequence-Commutative-Ring =
    head-fin-sequence-Ring (ring-Commutative-Ring R)

  tail-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence-Commutative-Ring (succ-ℕ n) →
    fin-sequence-Commutative-Ring n
  tail-fin-sequence-Commutative-Ring =
    tail-fin-sequence-Ring (ring-Commutative-Ring R)

  cons-fin-sequence-Commutative-Ring :
    (n : ℕ) → type-Commutative-Ring R →
    fin-sequence-Commutative-Ring n →
    fin-sequence-Commutative-Ring (succ-ℕ n)
  cons-fin-sequence-Commutative-Ring =
    cons-fin-sequence-Ring (ring-Commutative-Ring R)

  snoc-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence-Commutative-Ring n →
    type-Commutative-Ring R → fin-sequence-Commutative-Ring (succ-ℕ n)
  snoc-fin-sequence-Commutative-Ring =
    snoc-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Zero finite sequence on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence-Commutative-Ring R n
  zero-fin-sequence-Commutative-Ring n i = zero-Commutative-Ring R
```

### Pointwise addition on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v w : fin-sequence-Commutative-Ring R n) →
    fin-sequence-Commutative-Ring R n
  add-fin-sequence-Commutative-Ring =
    add-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Pointwise negation on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  neg-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence-Commutative-Ring R n →
    fin-sequence-Commutative-Ring R n
  neg-fin-sequence-Commutative-Ring =
    neg-fin-sequence-Ring (ring-Commutative-Ring R)
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-Commutative-Ring R n) →
    ( add-fin-sequence-Commutative-Ring R n
      ( add-fin-sequence-Commutative-Ring R n v1 v2) v3) ＝
    ( add-fin-sequence-Commutative-Ring R n v1
      ( add-fin-sequence-Commutative-Ring R n v2 v3))
  associative-add-fin-sequence-Commutative-Ring =
    associative-add-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-Commutative-Ring R n) →
    add-fin-sequence-Commutative-Ring R n
      ( zero-fin-sequence-Commutative-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-Commutative-Ring =
    left-unit-law-add-fin-sequence-Ring (ring-Commutative-Ring R)

  right-unit-law-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-Commutative-Ring R n) →
    add-fin-sequence-Commutative-Ring R n v
      ( zero-fin-sequence-Commutative-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-Commutative-Ring =
    right-unit-law-add-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v w : fin-sequence-Commutative-Ring R n) →
    add-fin-sequence-Commutative-Ring R n v w ＝
    add-fin-sequence-Commutative-Ring R n w v
  commutative-add-fin-sequence-Commutative-Ring =
    commutative-add-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Inverse laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-inverse-law-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-Commutative-Ring R n) →
    add-fin-sequence-Commutative-Ring
      ( R)
      ( n)
      ( neg-fin-sequence-Commutative-Ring R n v)
      ( v) ＝
    zero-fin-sequence-Commutative-Ring R n
  left-inverse-law-add-fin-sequence-Commutative-Ring =
    left-inverse-law-add-fin-sequence-Ring (ring-Commutative-Ring R)

  right-inverse-law-add-fin-sequence-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-Commutative-Ring R n) →
    add-fin-sequence-Commutative-Ring
      ( R)
      ( n)
      ( v)
      ( neg-fin-sequence-Commutative-Ring R n v) ＝
    zero-fin-sequence-Commutative-Ring R n
  right-inverse-law-add-fin-sequence-Commutative-Ring =
    right-inverse-law-add-fin-sequence-Ring (ring-Commutative-Ring R)
```

### Abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  fin-sequence-Commutative-Ring-Semigroup : ℕ → Semigroup l
  fin-sequence-Commutative-Ring-Semigroup =
    fin-sequence-Ring-Semigroup (ring-Commutative-Ring R)

  fin-sequence-Commutative-Ring-Monoid : ℕ → Monoid l
  fin-sequence-Commutative-Ring-Monoid =
    fin-sequence-Ring-Monoid (ring-Commutative-Ring R)

  fin-sequence-Commutative-Ring-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  fin-sequence-Commutative-Ring-Commutative-Monoid =
    fin-sequence-Ring-Commutative-Monoid (ring-Commutative-Ring R)

  fin-sequence-Commutative-Ring-Group : ℕ → Group l
  fin-sequence-Commutative-Ring-Group =
    fin-sequence-Ring-Group (ring-Commutative-Ring R)

  fin-sequence-Commutative-Ring-Ab : ℕ → Ab l
  fin-sequence-Commutative-Ring-Ab =
    fin-sequence-Ring-Ab (ring-Commutative-Ring R)
```
