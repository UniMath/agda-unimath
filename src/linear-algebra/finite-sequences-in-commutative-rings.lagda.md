# Finite sequences in commutative rings

```agda
module linear-algebra.finite-sequences-in-commutative-rings where
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

open import linear-algebra.finite-sequences-in-rings
```

</details>

## Idea

Finite sequences in a
[commutative ring](commutative-algebra.commutative-rings.md) `R` are
[finite sequences](lists.finite-sequences.md) in the underlying type of `R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  fin-sequence-type-Commutative-Ring : ℕ → UU l
  fin-sequence-type-Commutative-Ring =
    fin-sequence-type-Ring (ring-Commutative-Ring R)

  head-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → fin-sequence-type-Commutative-Ring (succ-ℕ n) →
    type-Commutative-Ring R
  head-fin-sequence-type-Commutative-Ring =
    head-fin-sequence-type-Ring (ring-Commutative-Ring R)

  tail-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → fin-sequence-type-Commutative-Ring (succ-ℕ n) →
    fin-sequence-type-Commutative-Ring n
  tail-fin-sequence-type-Commutative-Ring =
    tail-fin-sequence-type-Ring (ring-Commutative-Ring R)

  cons-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → type-Commutative-Ring R →
    fin-sequence-type-Commutative-Ring n →
    fin-sequence-type-Commutative-Ring (succ-ℕ n)
  cons-fin-sequence-type-Commutative-Ring =
    cons-fin-sequence-type-Ring (ring-Commutative-Ring R)

  snoc-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → fin-sequence-type-Commutative-Ring n →
    type-Commutative-Ring R → fin-sequence-type-Commutative-Ring (succ-ℕ n)
  snoc-fin-sequence-type-Commutative-Ring =
    snoc-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### The zero finite sequence in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → fin-sequence-type-Commutative-Ring R n
  zero-fin-sequence-type-Commutative-Ring n i = zero-Commutative-Ring R
```

### Pointwise addition of finite sequences in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Ring R n) →
    fin-sequence-type-Commutative-Ring R n
  add-fin-sequence-type-Commutative-Ring =
    add-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Pointwise negation of finite sequences in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  neg-fin-sequence-type-Commutative-Ring :
    (n : ℕ) → fin-sequence-type-Commutative-Ring R n →
    fin-sequence-type-Commutative-Ring R n
  neg-fin-sequence-type-Commutative-Ring =
    neg-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Commutative-Ring R n) →
    ( add-fin-sequence-type-Commutative-Ring R n
      ( add-fin-sequence-type-Commutative-Ring R n v1 v2) v3) ＝
    ( add-fin-sequence-type-Commutative-Ring R n v1
      ( add-fin-sequence-type-Commutative-Ring R n v2 v3))
  associative-add-fin-sequence-type-Commutative-Ring =
    associative-add-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Ring R n) →
    add-fin-sequence-type-Commutative-Ring R n
      ( zero-fin-sequence-type-Commutative-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-type-Commutative-Ring =
    left-unit-law-add-fin-sequence-type-Ring (ring-Commutative-Ring R)

  right-unit-law-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Ring R n) →
    add-fin-sequence-type-Commutative-Ring R n v
      ( zero-fin-sequence-type-Commutative-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-type-Commutative-Ring =
    right-unit-law-add-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Ring R n) →
    add-fin-sequence-type-Commutative-Ring R n v w ＝
    add-fin-sequence-type-Commutative-Ring R n w v
  commutative-add-fin-sequence-type-Commutative-Ring =
    commutative-add-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Inverse laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-inverse-law-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Ring R n) →
    add-fin-sequence-type-Commutative-Ring
      ( R)
      ( n)
      ( neg-fin-sequence-type-Commutative-Ring R n v)
      ( v) ＝
    zero-fin-sequence-type-Commutative-Ring R n
  left-inverse-law-add-fin-sequence-type-Commutative-Ring =
    left-inverse-law-add-fin-sequence-type-Ring (ring-Commutative-Ring R)

  right-inverse-law-add-fin-sequence-type-Commutative-Ring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Ring R n) →
    add-fin-sequence-type-Commutative-Ring
      ( R)
      ( n)
      ( v)
      ( neg-fin-sequence-type-Commutative-Ring R n v) ＝
    zero-fin-sequence-type-Commutative-Ring R n
  right-inverse-law-add-fin-sequence-type-Commutative-Ring =
    right-inverse-law-add-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  semigroup-fin-sequence-type-Commutative-Ring : ℕ → Semigroup l
  semigroup-fin-sequence-type-Commutative-Ring =
    semigroup-fin-sequence-type-Ring (ring-Commutative-Ring R)

  monoid-fin-sequence-type-Commutative-Ring : ℕ → Monoid l
  monoid-fin-sequence-type-Commutative-Ring =
    monoid-fin-sequence-type-Ring (ring-Commutative-Ring R)

  commutative-monoid-fin-sequence-type-Commutative-Ring :
    ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Commutative-Ring =
    commutative-monoid-fin-sequence-type-Ring (ring-Commutative-Ring R)

  group-fin-sequence-type-Commutative-Ring : ℕ → Group l
  group-fin-sequence-type-Commutative-Ring =
    group-fin-sequence-type-Ring (ring-Commutative-Ring R)

  ab-fin-sequence-type-Commutative-Ring : ℕ → Ab l
  ab-fin-sequence-type-Commutative-Ring =
    ab-fin-sequence-type-Ring (ring-Commutative-Ring R)
```
