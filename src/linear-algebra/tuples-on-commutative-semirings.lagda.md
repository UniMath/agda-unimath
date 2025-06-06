# Tuples on commutative semirings

```agda
module linear-algebra.tuples-on-commutative-semirings where
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

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-semirings
```

</details>

## Idea

Tuples on a [commutative semiring](commutative-algebra.commutative-semirings.md)
`R` are [tuples](lists.tuples.md) on the underlying type of `R`. The commutative
semiring structure on `R` induces further structure on the type of tuples on
`R`.

## Definitions

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  tuple-Commutative-Semiring : ℕ → UU l
  tuple-Commutative-Semiring =
    tuple-Semiring (semiring-Commutative-Semiring R)

  head-tuple-Commutative-Semiring :
    {n : ℕ} → tuple-Commutative-Semiring (succ-ℕ n) →
    type-Commutative-Semiring R
  head-tuple-Commutative-Semiring =
    head-tuple-Semiring (semiring-Commutative-Semiring R)

  tail-tuple-Commutative-Semiring :
    {n : ℕ} → tuple-Commutative-Semiring (succ-ℕ n) →
    tuple-Commutative-Semiring n
  tail-tuple-Commutative-Semiring =
    tail-tuple-Semiring (semiring-Commutative-Semiring R)

  snoc-tuple-Commutative-Semiring :
    {n : ℕ} → tuple-Commutative-Semiring n → type-Commutative-Semiring R →
    tuple-Commutative-Semiring (succ-ℕ n)
  snoc-tuple-Commutative-Semiring =
    snoc-tuple-Semiring (semiring-Commutative-Semiring R)
```

### The zero tuple in a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-tuple-Commutative-Semiring : {n : ℕ} → tuple-Commutative-Semiring R n
  zero-tuple-Commutative-Semiring = constant-tuple (zero-Commutative-Semiring R)
```

### Pointwise addition of tuples on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-tuple-Commutative-Semiring :
    {n : ℕ} → tuple-Commutative-Semiring R n → tuple-Commutative-Semiring R n →
    tuple-Commutative-Semiring R n
  add-tuple-Commutative-Semiring =
    add-tuple-Semiring (semiring-Commutative-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  associative-add-tuple-Commutative-Semiring :
    {n : ℕ} (v1 v2 v3 : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring
      R (add-tuple-Commutative-Semiring R v1 v2) v3 ＝
    add-tuple-Commutative-Semiring R v1 (add-tuple-Commutative-Semiring R v2 v3)
  associative-add-tuple-Commutative-Semiring =
    associative-add-tuple-Semiring (semiring-Commutative-Semiring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-unit-law-add-tuple-Commutative-Semiring :
    {n : ℕ} (v : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring R (zero-tuple-Commutative-Semiring R) v ＝ v
  left-unit-law-add-tuple-Commutative-Semiring =
    left-unit-law-add-tuple-Semiring (semiring-Commutative-Semiring R)

  right-unit-law-add-tuple-Commutative-Semiring :
    {n : ℕ} (v : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring R v (zero-tuple-Commutative-Semiring R) ＝ v
  right-unit-law-add-tuple-Commutative-Semiring =
    right-unit-law-add-tuple-Semiring (semiring-Commutative-Semiring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  commutative-add-tuple-Commutative-Semiring :
    {n : ℕ} (v w : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring R v w ＝ add-tuple-Commutative-Semiring R w v
  commutative-add-tuple-Commutative-Semiring =
    commutative-add-tuple-Semiring (semiring-Commutative-Semiring R)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  tuple-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  tuple-Commutative-Semiring-Semigroup =
    semigroup-tuple-Semiring (semiring-Commutative-Semiring R)

  tuple-Commutative-Semiring-Monoid : ℕ → Monoid l
  tuple-Commutative-Semiring-Monoid =
    monoid-tuple-Semiring (semiring-Commutative-Semiring R)

  tuple-Commutative-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Commutative-Semiring-Commutative-Monoid =
    commutative-monoid-tuple-Semiring (semiring-Commutative-Semiring R)
```
