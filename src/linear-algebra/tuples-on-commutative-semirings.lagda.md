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
`R` are [tuples](linear-algebra.tuples.md) on the underlying type of `R`. The
commutative semiring structure on `R` induces further structure on the type of
tuples on `R`.

## Definitions

### Listed tuples on commutative semirings

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

### Functional tuples on commutative semirings

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  functional-tuple-Commutative-Semiring : ℕ → UU l
  functional-tuple-Commutative-Semiring =
    functional-tuple-Semiring (semiring-Commutative-Semiring R)

  head-functional-tuple-Commutative-Semiring :
    (n : ℕ) → functional-tuple-Commutative-Semiring (succ-ℕ n) →
    type-Commutative-Semiring R
  head-functional-tuple-Commutative-Semiring =
    head-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  tail-functional-tuple-Commutative-Semiring :
    (n : ℕ) → functional-tuple-Commutative-Semiring (succ-ℕ n) →
    functional-tuple-Commutative-Semiring n
  tail-functional-tuple-Commutative-Semiring =
    tail-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  cons-functional-tuple-Commutative-Semiring :
    (n : ℕ) → type-Commutative-Semiring R →
    functional-tuple-Commutative-Semiring n →
    functional-tuple-Commutative-Semiring (succ-ℕ n)
  cons-functional-tuple-Commutative-Semiring =
    cons-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  snoc-functional-tuple-Commutative-Semiring :
    (n : ℕ) → functional-tuple-Commutative-Semiring n →
    type-Commutative-Semiring R →
    functional-tuple-Commutative-Semiring (succ-ℕ n)
  snoc-functional-tuple-Commutative-Semiring =
    snoc-functional-tuple-Semiring (semiring-Commutative-Semiring R)
```

### Zero tuple on a commutative semiring

#### The zero listed tuple

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-tuple-Commutative-Semiring : {n : ℕ} → tuple-Commutative-Semiring R n
  zero-tuple-Commutative-Semiring = constant-tuple (zero-Commutative-Semiring R)
```

#### The zero functional tuple

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-functional-tuple-Commutative-Semiring :
    (n : ℕ) → functional-tuple-Commutative-Semiring R n
  zero-functional-tuple-Commutative-Semiring n i = zero-Commutative-Semiring R
```

### Pointwise addition of tuples on a commutative semiring

#### Pointwise addition of listed tuples on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-tuple-Commutative-Semiring :
    {n : ℕ} → tuple-Commutative-Semiring R n → tuple-Commutative-Semiring R n →
    tuple-Commutative-Semiring R n
  add-tuple-Commutative-Semiring =
    add-tuple-Semiring (semiring-Commutative-Semiring R)

  associative-add-tuple-Commutative-Semiring :
    {n : ℕ} (v1 v2 v3 : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring (add-tuple-Commutative-Semiring v1 v2) v3 ＝
    add-tuple-Commutative-Semiring v1 (add-tuple-Commutative-Semiring v2 v3)
  associative-add-tuple-Commutative-Semiring =
    associative-add-tuple-Semiring (semiring-Commutative-Semiring R)

  tuple-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  tuple-Commutative-Semiring-Semigroup =
    tuple-Semiring-Semigroup (semiring-Commutative-Semiring R)

  left-unit-law-add-tuple-Commutative-Semiring :
    {n : ℕ} (v : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring (zero-tuple-Commutative-Semiring R) v ＝ v
  left-unit-law-add-tuple-Commutative-Semiring =
    left-unit-law-add-tuple-Semiring (semiring-Commutative-Semiring R)

  right-unit-law-add-tuple-Commutative-Semiring :
    {n : ℕ} (v : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring v (zero-tuple-Commutative-Semiring R) ＝ v
  right-unit-law-add-tuple-Commutative-Semiring =
    right-unit-law-add-tuple-Semiring (semiring-Commutative-Semiring R)

  tuple-Commutative-Semiring-Monoid : ℕ → Monoid l
  tuple-Commutative-Semiring-Monoid =
    tuple-Semiring-Monoid (semiring-Commutative-Semiring R)

  commutative-add-tuple-Commutative-Semiring :
    {n : ℕ} (v w : tuple-Commutative-Semiring R n) →
    add-tuple-Commutative-Semiring v w ＝ add-tuple-Commutative-Semiring w v
  commutative-add-tuple-Commutative-Semiring =
    commutative-add-tuple-Semiring (semiring-Commutative-Semiring R)

  tuple-Commutative-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Commutative-Semiring-Commutative-Monoid =
    tuple-Semiring-Commutative-Monoid (semiring-Commutative-Semiring R)
```

#### Pointwise addition of functional tuples on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-functional-tuple-Commutative-Semiring :
    (n : ℕ) (v w : functional-tuple-Commutative-Semiring R n) →
    functional-tuple-Commutative-Semiring R n
  add-functional-tuple-Commutative-Semiring =
    add-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  associative-add-functional-tuple-Commutative-Semiring :
    (n : ℕ) (v1 v2 v3 : functional-tuple-Commutative-Semiring R n) →
    ( add-functional-tuple-Commutative-Semiring n
      ( add-functional-tuple-Commutative-Semiring n v1 v2) v3) ＝
    ( add-functional-tuple-Commutative-Semiring n v1
      ( add-functional-tuple-Commutative-Semiring n v2 v3))
  associative-add-functional-tuple-Commutative-Semiring =
    associative-add-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  functional-tuple-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  functional-tuple-Commutative-Semiring-Semigroup =
    functional-tuple-Semiring-Semigroup (semiring-Commutative-Semiring R)

  left-unit-law-add-functional-tuple-Commutative-Semiring :
    (n : ℕ) (v : functional-tuple-Commutative-Semiring R n) →
    add-functional-tuple-Commutative-Semiring n
      ( zero-functional-tuple-Commutative-Semiring R n) v ＝ v
  left-unit-law-add-functional-tuple-Commutative-Semiring =
    left-unit-law-add-functional-tuple-Semiring
      ( semiring-Commutative-Semiring R)

  right-unit-law-add-functional-tuple-Commutative-Semiring :
    (n : ℕ) (v : functional-tuple-Commutative-Semiring R n) →
    add-functional-tuple-Commutative-Semiring n v
      ( zero-functional-tuple-Commutative-Semiring R n) ＝ v
  right-unit-law-add-functional-tuple-Commutative-Semiring =
    right-unit-law-add-functional-tuple-Semiring
      ( semiring-Commutative-Semiring R)

  functional-tuple-Commutative-Semiring-Monoid : ℕ → Monoid l
  functional-tuple-Commutative-Semiring-Monoid =
    functional-tuple-Semiring-Monoid (semiring-Commutative-Semiring R)

  commutative-add-functional-tuple-Commutative-Semiring :
    (n : ℕ) (v w : functional-tuple-Commutative-Semiring R n) →
    add-functional-tuple-Commutative-Semiring n v w ＝
    add-functional-tuple-Commutative-Semiring n w v
  commutative-add-functional-tuple-Commutative-Semiring =
    commutative-add-functional-tuple-Semiring (semiring-Commutative-Semiring R)

  functional-tuple-Commutative-Semiring-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  functional-tuple-Commutative-Semiring-Commutative-Monoid =
    functional-tuple-Semiring-Commutative-Monoid
      ( semiring-Commutative-Semiring R)
```
