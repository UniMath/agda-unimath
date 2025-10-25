# Finite sequences in commutative semirings

```agda
module linear-algebra.finite-sequences-in-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semirings
```

</details>

## Idea

Finite sequences in a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` are
[finite sequences](lists.finite-sequences.md) in the underlying type of `R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  fin-sequence-type-Commutative-Semiring : ℕ → UU l
  fin-sequence-type-Commutative-Semiring =
    fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  head-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) → fin-sequence-type-Commutative-Semiring (succ-ℕ n) →
    type-Commutative-Semiring R
  head-fin-sequence-type-Commutative-Semiring =
    head-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  tail-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) → fin-sequence-type-Commutative-Semiring (succ-ℕ n) →
    fin-sequence-type-Commutative-Semiring n
  tail-fin-sequence-type-Commutative-Semiring =
    tail-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  cons-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) → type-Commutative-Semiring R →
    fin-sequence-type-Commutative-Semiring n →
    fin-sequence-type-Commutative-Semiring (succ-ℕ n)
  cons-fin-sequence-type-Commutative-Semiring =
    cons-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  snoc-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) → fin-sequence-type-Commutative-Semiring n →
    type-Commutative-Semiring R →
    fin-sequence-type-Commutative-Semiring (succ-ℕ n)
  snoc-fin-sequence-type-Commutative-Semiring =
    snoc-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

### The zero finite sequence in a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) → fin-sequence-type-Commutative-Semiring R n
  zero-fin-sequence-type-Commutative-Semiring n i = zero-Commutative-Semiring R
```

#### Pointwise addition of finite sequences in a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Semiring R n) →
    fin-sequence-type-Commutative-Semiring R n
  add-fin-sequence-type-Commutative-Semiring =
    add-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  associative-add-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Commutative-Semiring R n) →
    add-fin-sequence-type-Commutative-Semiring R n
      ( add-fin-sequence-type-Commutative-Semiring R n v1 v2)
      ( v3) ＝
    add-fin-sequence-type-Commutative-Semiring R n
      ( v1)
      ( add-fin-sequence-type-Commutative-Semiring R n v2 v3)
  associative-add-fin-sequence-type-Commutative-Semiring =
    associative-add-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-unit-law-add-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Semiring R n) →
    add-fin-sequence-type-Commutative-Semiring R n
      ( zero-fin-sequence-type-Commutative-Semiring R n) v ＝ v
  left-unit-law-add-fin-sequence-type-Commutative-Semiring =
    left-unit-law-add-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)

  right-unit-law-add-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (v : fin-sequence-type-Commutative-Semiring R n) →
    add-fin-sequence-type-Commutative-Semiring R n v
      ( zero-fin-sequence-type-Commutative-Semiring R n) ＝ v
  right-unit-law-add-fin-sequence-type-Commutative-Semiring =
    right-unit-law-add-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  commutative-add-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Semiring R n) →
    add-fin-sequence-type-Commutative-Semiring R n v w ＝
    add-fin-sequence-type-Commutative-Semiring R n w v
  commutative-add-fin-sequence-type-Commutative-Semiring =
    commutative-add-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  semigroup-fin-sequence-type-Commutative-Semiring : ℕ → Semigroup l
  semigroup-fin-sequence-type-Commutative-Semiring =
    semigroup-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  monoid-fin-sequence-type-Commutative-Semiring : ℕ → Monoid l
  monoid-fin-sequence-type-Commutative-Semiring =
    monoid-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)

  commutative-monoid-fin-sequence-type-Commutative-Semiring :
    ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Commutative-Semiring =
    commutative-monoid-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)
```
