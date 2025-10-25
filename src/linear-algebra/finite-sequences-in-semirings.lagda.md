# Finite sequences in semirings

```agda
module linear-algebra.finite-sequences-in-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-commutative-monoids

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import ring-theory.semirings
```

</details>

## Idea

Given a [semiring](ring-theory.semirings.md) `R`, the type
`finite-sequence-Semiring R n` of [finite sequences](lists.finite-sequences.md)
of length `n` in the underlying type of `R` is a
[commutative monoid](group-theory.commutative-monoids.md) under addition.

## Definitions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  fin-sequence-type-Semiring : ℕ → UU l
  fin-sequence-type-Semiring = fin-sequence (type-Semiring R)

  head-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring (succ-ℕ n) → type-Semiring R
  head-fin-sequence-type-Semiring n v = head-fin-sequence n v

  tail-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring (succ-ℕ n) →
    fin-sequence-type-Semiring n
  tail-fin-sequence-type-Semiring = tail-fin-sequence

  cons-fin-sequence-type-Semiring :
    (n : ℕ) → type-Semiring R →
    fin-sequence-type-Semiring n → fin-sequence-type-Semiring (succ-ℕ n)
  cons-fin-sequence-type-Semiring = cons-fin-sequence

  snoc-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring n → type-Semiring R →
    fin-sequence-type-Semiring (succ-ℕ n)
  snoc-fin-sequence-type-Semiring = snoc-fin-sequence
```

### The zero finite sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-fin-sequence-type-Semiring : (n : ℕ) → fin-sequence-type-Semiring R n
  zero-fin-sequence-type-Semiring n i = zero-Semiring R
```

### Pointwise addition of finite sequences in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-fin-sequence-type-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Semiring R n) →
    fin-sequence-type-Semiring R n
  add-fin-sequence-type-Semiring =
    add-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  associative-add-fin-sequence-type-Semiring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R
      ( n)
      ( add-fin-sequence-type-Semiring R n v1 v2)
      ( v3) ＝
    add-fin-sequence-type-Semiring R
      ( n)
      ( v1)
      ( add-fin-sequence-type-Semiring R n v2 v3)
  associative-add-fin-sequence-type-Semiring =
    associative-add-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-unit-law-add-fin-sequence-type-Semiring :
    (n : ℕ) (v : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n
      ( zero-fin-sequence-type-Semiring R n)
      ( v) ＝
    v
  left-unit-law-add-fin-sequence-type-Semiring =
    left-unit-law-add-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-unit-law-add-fin-sequence-type-Semiring :
    (n : ℕ) (v : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n
      ( v)
      ( zero-fin-sequence-type-Semiring R n) ＝
    v
  right-unit-law-add-fin-sequence-type-Semiring =
    right-unit-law-add-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commutative-add-fin-sequence-type-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n v w ＝
    add-fin-sequence-type-Semiring R n w v
  commutative-add-fin-sequence-type-Semiring =
    commutative-add-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  semigroup-fin-sequence-type-Semiring : ℕ → Semigroup l
  semigroup-fin-sequence-type-Semiring =
    semigroup-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  monoid-fin-sequence-type-Semiring : ℕ → Monoid l
  monoid-fin-sequence-type-Semiring =
    monoid-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  commutative-monoid-fin-sequence-type-Semiring : ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Semiring =
    commutative-monoid-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```
