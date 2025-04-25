# Finite sequences on commutative semirings

```agda
module linear-algebra.finite-sequences-on-commutative-semirings where
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

open import linear-algebra.finite-sequences-on-semirings
```

</details>

## Idea

Finite sequences on a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` are
[finite sequences](linear-algebra.finite-sequences.md) on the underlying type of
`R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  fin-sequence-Commutative-Semiring : ℕ → UU l
  fin-sequence-Commutative-Semiring =
    fin-sequence-Semiring (semiring-Commutative-Semiring R)

  head-fin-sequence-Commutative-Semiring :
    (n : ℕ) → fin-sequence-Commutative-Semiring (succ-ℕ n) →
    type-Commutative-Semiring R
  head-fin-sequence-Commutative-Semiring =
    head-fin-sequence-Semiring (semiring-Commutative-Semiring R)

  tail-fin-sequence-Commutative-Semiring :
    (n : ℕ) → fin-sequence-Commutative-Semiring (succ-ℕ n) →
    fin-sequence-Commutative-Semiring n
  tail-fin-sequence-Commutative-Semiring =
    tail-fin-sequence-Semiring (semiring-Commutative-Semiring R)

  cons-fin-sequence-Commutative-Semiring :
    (n : ℕ) → type-Commutative-Semiring R →
    fin-sequence-Commutative-Semiring n →
    fin-sequence-Commutative-Semiring (succ-ℕ n)
  cons-fin-sequence-Commutative-Semiring =
    cons-fin-sequence-Semiring (semiring-Commutative-Semiring R)

  snoc-fin-sequence-Commutative-Semiring :
    (n : ℕ) → fin-sequence-Commutative-Semiring n →
    type-Commutative-Semiring R →
    fin-sequence-Commutative-Semiring (succ-ℕ n)
  snoc-fin-sequence-Commutative-Semiring =
    snoc-fin-sequence-Semiring (semiring-Commutative-Semiring R)
```

### Zero finite sequence on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-fin-sequence-Commutative-Semiring :
    (n : ℕ) → fin-sequence-Commutative-Semiring R n
  zero-fin-sequence-Commutative-Semiring n i = zero-Commutative-Semiring R
```

#### Pointwise addition of finite sequences on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-fin-sequence-Commutative-Semiring :
    (n : ℕ) (v w : fin-sequence-Commutative-Semiring R n) →
    fin-sequence-Commutative-Semiring R n
  add-fin-sequence-Commutative-Semiring =
    add-fin-sequence-Semiring (semiring-Commutative-Semiring R)
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  associative-add-fin-sequence-Commutative-Semiring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-Commutative-Semiring R n) →
    ( add-fin-sequence-Commutative-Semiring R n
      ( add-fin-sequence-Commutative-Semiring R n v1 v2) v3) ＝
    ( add-fin-sequence-Commutative-Semiring R n v1
      ( add-fin-sequence-Commutative-Semiring R n v2 v3))
  associative-add-fin-sequence-Commutative-Semiring =
    associative-add-fin-sequence-Semiring (semiring-Commutative-Semiring R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-unit-law-add-fin-sequence-Commutative-Semiring :
    (n : ℕ) (v : fin-sequence-Commutative-Semiring R n) →
    add-fin-sequence-Commutative-Semiring R n
      ( zero-fin-sequence-Commutative-Semiring R n) v ＝ v
  left-unit-law-add-fin-sequence-Commutative-Semiring =
    left-unit-law-add-fin-sequence-Semiring
      ( semiring-Commutative-Semiring R)

  right-unit-law-add-fin-sequence-Commutative-Semiring :
    (n : ℕ) (v : fin-sequence-Commutative-Semiring R n) →
    add-fin-sequence-Commutative-Semiring R n v
      ( zero-fin-sequence-Commutative-Semiring R n) ＝ v
  right-unit-law-add-fin-sequence-Commutative-Semiring =
    right-unit-law-add-fin-sequence-Semiring
      ( semiring-Commutative-Semiring R)
```

### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  commutative-add-fin-sequence-Commutative-Semiring :
    (n : ℕ) (v w : fin-sequence-Commutative-Semiring R n) →
    add-fin-sequence-Commutative-Semiring R n v w ＝
    add-fin-sequence-Commutative-Semiring R n w v
  commutative-add-fin-sequence-Commutative-Semiring =
    commutative-add-fin-sequence-Semiring (semiring-Commutative-Semiring R)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  fin-sequence-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  fin-sequence-Commutative-Semiring-Semigroup =
    fin-sequence-Semiring-Semigroup (semiring-Commutative-Semiring R)

  fin-sequence-Commutative-Semiring-Monoid : ℕ → Monoid l
  fin-sequence-Commutative-Semiring-Monoid =
    fin-sequence-Semiring-Monoid (semiring-Commutative-Semiring R)

  fin-sequence-Commutative-Semiring-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  fin-sequence-Commutative-Semiring-Commutative-Monoid =
    fin-sequence-Semiring-Commutative-Monoid
      ( semiring-Commutative-Semiring R)
```
