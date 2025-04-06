# Tuples on commutative rings

```agda
module linear-algebra.tuples-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-rings
```

</details>

## Idea

Tuples on a commutative ring `R` are tuples on the underlying type of `R`. The
commutative ring structure on `R` induces further structure on the type of
tuples on `R`.

## Definitions

### Listed tuples on commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  tuple-Commutative-Ring : ℕ → UU l
  tuple-Commutative-Ring = tuple-Ring (ring-Commutative-Ring R)

  head-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring (succ-ℕ n) → type-Commutative-Ring R
  head-tuple-Commutative-Ring = head-tuple-Ring (ring-Commutative-Ring R)

  tail-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring (succ-ℕ n) → tuple-Commutative-Ring n
  tail-tuple-Commutative-Ring = tail-tuple-Ring (ring-Commutative-Ring R)

  snoc-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring n → type-Commutative-Ring R →
    tuple-Commutative-Ring (succ-ℕ n)
  snoc-tuple-Commutative-Ring = snoc-tuple-Ring (ring-Commutative-Ring R)
```

### Functional tuples on commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  functional-tuple-Commutative-Ring : ℕ → UU l
  functional-tuple-Commutative-Ring =
    functional-tuple-Ring (ring-Commutative-Ring R)

  head-functional-tuple-Commutative-Ring :
    (n : ℕ) → functional-tuple-Commutative-Ring (succ-ℕ n) →
    type-Commutative-Ring R
  head-functional-tuple-Commutative-Ring =
    head-functional-tuple-Ring (ring-Commutative-Ring R)

  tail-functional-tuple-Commutative-Ring :
    (n : ℕ) → functional-tuple-Commutative-Ring (succ-ℕ n) →
    functional-tuple-Commutative-Ring n
  tail-functional-tuple-Commutative-Ring =
    tail-functional-tuple-Ring (ring-Commutative-Ring R)

  cons-functional-tuple-Commutative-Ring :
    (n : ℕ) → type-Commutative-Ring R →
    functional-tuple-Commutative-Ring n →
    functional-tuple-Commutative-Ring (succ-ℕ n)
  cons-functional-tuple-Commutative-Ring =
    cons-functional-tuple-Ring (ring-Commutative-Ring R)

  snoc-functional-tuple-Commutative-Ring :
    (n : ℕ) → functional-tuple-Commutative-Ring n →
    type-Commutative-Ring R → functional-tuple-Commutative-Ring (succ-ℕ n)
  snoc-functional-tuple-Commutative-Ring =
    snoc-functional-tuple-Ring (ring-Commutative-Ring R)
```

### Zero tuple on a commutative ring

#### The zero listed tuple

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-tuple-Commutative-Ring : {n : ℕ} → tuple-Commutative-Ring R n
  zero-tuple-Commutative-Ring = constant-tuple (zero-Commutative-Ring R)
```

#### The zero functional tuple

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-functional-tuple-Commutative-Ring :
    (n : ℕ) → functional-tuple-Commutative-Ring R n
  zero-functional-tuple-Commutative-Ring n i = zero-Commutative-Ring R
```

### Pointwise addition of tuples on a commutative ring

#### Pointwise addition of listed tuples on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring R n → tuple-Commutative-Ring R n →
    tuple-Commutative-Ring R n
  add-tuple-Commutative-Ring =
    add-tuple-Ring (ring-Commutative-Ring R)

  associative-add-tuple-Commutative-Ring :
    {n : ℕ} (v1 v2 v3 : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring (add-tuple-Commutative-Ring v1 v2) v3 ＝
    add-tuple-Commutative-Ring v1 (add-tuple-Commutative-Ring v2 v3)
  associative-add-tuple-Commutative-Ring =
    associative-add-tuple-Ring (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Semigroup : ℕ → Semigroup l
  tuple-Commutative-Ring-Semigroup =
    tuple-Ring-Semigroup (ring-Commutative-Ring R)

  left-unit-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring (zero-tuple-Commutative-Ring R) v ＝ v
  left-unit-law-add-tuple-Commutative-Ring =
    left-unit-law-add-tuple-Ring (ring-Commutative-Ring R)

  right-unit-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring v (zero-tuple-Commutative-Ring R) ＝ v
  right-unit-law-add-tuple-Commutative-Ring =
    right-unit-law-add-tuple-Ring (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Monoid : ℕ → Monoid l
  tuple-Commutative-Ring-Monoid =
    tuple-Ring-Monoid (ring-Commutative-Ring R)

  commutative-add-tuple-Commutative-Ring :
    {n : ℕ} (v w : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring v w ＝ add-tuple-Commutative-Ring w v
  commutative-add-tuple-Commutative-Ring =
    commutative-add-tuple-Ring (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Commutative-Ring-Commutative-Monoid =
    tuple-Ring-Commutative-Monoid (ring-Commutative-Ring R)
```

#### Pointwise addition of functional tuples on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-functional-tuple-Commutative-Ring :
    (n : ℕ) (v w : functional-tuple-Commutative-Ring R n) →
    functional-tuple-Commutative-Ring R n
  add-functional-tuple-Commutative-Ring =
    add-functional-tuple-Ring (ring-Commutative-Ring R)

  associative-add-functional-tuple-Commutative-Ring :
    (n : ℕ) (v1 v2 v3 : functional-tuple-Commutative-Ring R n) →
    ( add-functional-tuple-Commutative-Ring n
      ( add-functional-tuple-Commutative-Ring n v1 v2) v3) ＝
    ( add-functional-tuple-Commutative-Ring n v1
      ( add-functional-tuple-Commutative-Ring n v2 v3))
  associative-add-functional-tuple-Commutative-Ring =
    associative-add-functional-tuple-Ring (ring-Commutative-Ring R)

  functional-tuple-Commutative-Ring-Semigroup : ℕ → Semigroup l
  functional-tuple-Commutative-Ring-Semigroup =
    functional-tuple-Ring-Semigroup (ring-Commutative-Ring R)

  left-unit-law-add-functional-tuple-Commutative-Ring :
    (n : ℕ) (v : functional-tuple-Commutative-Ring R n) →
    add-functional-tuple-Commutative-Ring n
      ( zero-functional-tuple-Commutative-Ring R n) v ＝ v
  left-unit-law-add-functional-tuple-Commutative-Ring =
    left-unit-law-add-functional-tuple-Ring (ring-Commutative-Ring R)

  right-unit-law-add-functional-tuple-Commutative-Ring :
    (n : ℕ) (v : functional-tuple-Commutative-Ring R n) →
    add-functional-tuple-Commutative-Ring n v
      ( zero-functional-tuple-Commutative-Ring R n) ＝ v
  right-unit-law-add-functional-tuple-Commutative-Ring =
    right-unit-law-add-functional-tuple-Ring (ring-Commutative-Ring R)

  functional-tuple-Commutative-Ring-Monoid : ℕ → Monoid l
  functional-tuple-Commutative-Ring-Monoid =
    functional-tuple-Ring-Monoid (ring-Commutative-Ring R)

  commutative-add-functional-tuple-Commutative-Ring :
    (n : ℕ) (v w : functional-tuple-Commutative-Ring R n) →
    add-functional-tuple-Commutative-Ring n v w ＝
    add-functional-tuple-Commutative-Ring n w v
  commutative-add-functional-tuple-Commutative-Ring =
    commutative-add-functional-tuple-Ring (ring-Commutative-Ring R)

  functional-tuple-Commutative-Ring-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  functional-tuple-Commutative-Ring-Commutative-Monoid =
    functional-tuple-Ring-Commutative-Monoid (ring-Commutative-Ring R)
```
