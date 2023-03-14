# Vectors on commutative rings

```agda
module linear-algebra.vectors-on-commutative-rings where
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

open import linear-algebra.constant-vectors
open import linear-algebra.vectors-on-rings
```

</details>

## Idea

Vectors on a commutative ring `R` are vectors on the underlying type of `R`. The
commutative ring structur on `R` induces further structure on the type of
vectors on `R`.

## Definitions

### Listed vectors on commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  vec-Commutative-Ring : ℕ → UU l
  vec-Commutative-Ring = vec-Ring (ring-Commutative-Ring R)

  head-vec-Commutative-Ring :
    {n : ℕ} → vec-Commutative-Ring (succ-ℕ n) → type-Commutative-Ring R
  head-vec-Commutative-Ring = head-vec-Ring (ring-Commutative-Ring R)

  tail-vec-Commutative-Ring :
    {n : ℕ} → vec-Commutative-Ring (succ-ℕ n) → vec-Commutative-Ring n
  tail-vec-Commutative-Ring = tail-vec-Ring (ring-Commutative-Ring R)

  snoc-vec-Commutative-Ring :
    {n : ℕ} → vec-Commutative-Ring n → type-Commutative-Ring R →
    vec-Commutative-Ring (succ-ℕ n)
  snoc-vec-Commutative-Ring = snoc-vec-Ring (ring-Commutative-Ring R)
```

### Functional vectors on commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  functional-vec-Commutative-Ring : ℕ → UU l
  functional-vec-Commutative-Ring =
    functional-vec-Ring (ring-Commutative-Ring R)

  head-functional-vec-Commutative-Ring :
    (n : ℕ) → functional-vec-Commutative-Ring (succ-ℕ n) →
    type-Commutative-Ring R
  head-functional-vec-Commutative-Ring =
    head-functional-vec-Ring (ring-Commutative-Ring R)

  tail-functional-vec-Commutative-Ring :
    (n : ℕ) → functional-vec-Commutative-Ring (succ-ℕ n) →
    functional-vec-Commutative-Ring n
  tail-functional-vec-Commutative-Ring =
    tail-functional-vec-Ring (ring-Commutative-Ring R)

  cons-functional-vec-Commutative-Ring :
    (n : ℕ) → type-Commutative-Ring R →
    functional-vec-Commutative-Ring n →
    functional-vec-Commutative-Ring (succ-ℕ n)
  cons-functional-vec-Commutative-Ring =
    cons-functional-vec-Ring (ring-Commutative-Ring R)

  snoc-functional-vec-Commutative-Ring :
    (n : ℕ) → functional-vec-Commutative-Ring n →
    type-Commutative-Ring R → functional-vec-Commutative-Ring (succ-ℕ n)
  snoc-functional-vec-Commutative-Ring =
    snoc-functional-vec-Ring (ring-Commutative-Ring R)
```

### Zero vector on a commutative ring

#### The zero listed vector

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-vec-Commutative-Ring : {n : ℕ} → vec-Commutative-Ring R n
  zero-vec-Commutative-Ring = constant-vec (zero-Commutative-Ring R)
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-functional-vec-Commutative-Ring :
    (n : ℕ) → functional-vec-Commutative-Ring R n
  zero-functional-vec-Commutative-Ring n i = zero-Commutative-Ring R
```

### Pointwise addition of vectors on a commutative ring

#### Pointwise addition of listed vectors on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-vec-Commutative-Ring :
    {n : ℕ} → vec-Commutative-Ring R n → vec-Commutative-Ring R n →
    vec-Commutative-Ring R n
  add-vec-Commutative-Ring =
    add-vec-Ring (ring-Commutative-Ring R)

  associative-add-vec-Commutative-Ring :
    {n : ℕ} (v1 v2 v3 : vec-Commutative-Ring R n) →
    add-vec-Commutative-Ring (add-vec-Commutative-Ring v1 v2) v3 ＝
    add-vec-Commutative-Ring v1 (add-vec-Commutative-Ring v2 v3)
  associative-add-vec-Commutative-Ring =
    associative-add-vec-Ring (ring-Commutative-Ring R)

  vec-Commutative-Ring-Semigroup : ℕ → Semigroup l
  vec-Commutative-Ring-Semigroup =
    vec-Ring-Semigroup (ring-Commutative-Ring R)

  left-unit-law-add-vec-Commutative-Ring :
    {n : ℕ} (v : vec-Commutative-Ring R n) →
    add-vec-Commutative-Ring (zero-vec-Commutative-Ring R) v ＝ v
  left-unit-law-add-vec-Commutative-Ring =
    left-unit-law-add-vec-Ring (ring-Commutative-Ring R)

  right-unit-law-add-vec-Commutative-Ring :
    {n : ℕ} (v : vec-Commutative-Ring R n) →
    add-vec-Commutative-Ring v (zero-vec-Commutative-Ring R) ＝ v
  right-unit-law-add-vec-Commutative-Ring =
    right-unit-law-add-vec-Ring (ring-Commutative-Ring R)

  vec-Commutative-Ring-Monoid : ℕ → Monoid l
  vec-Commutative-Ring-Monoid =
    vec-Ring-Monoid (ring-Commutative-Ring R)

  commutative-add-vec-Commutative-Ring :
    {n : ℕ} (v w : vec-Commutative-Ring R n) →
    add-vec-Commutative-Ring v w ＝ add-vec-Commutative-Ring w v
  commutative-add-vec-Commutative-Ring =
    commutative-add-vec-Ring (ring-Commutative-Ring R)

  vec-Commutative-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Commutative-Ring-Commutative-Monoid =
    vec-Ring-Commutative-Monoid (ring-Commutative-Ring R)
```

#### Pointwise addition of functional vectors on a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-functional-vec-Commutative-Ring :
    (n : ℕ) (v w : functional-vec-Commutative-Ring R n) →
    functional-vec-Commutative-Ring R n
  add-functional-vec-Commutative-Ring =
    add-functional-vec-Ring (ring-Commutative-Ring R)

  associative-add-functional-vec-Commutative-Ring :
    (n : ℕ) (v1 v2 v3 : functional-vec-Commutative-Ring R n) →
    ( add-functional-vec-Commutative-Ring n
      ( add-functional-vec-Commutative-Ring n v1 v2) v3) ＝
    ( add-functional-vec-Commutative-Ring n v1
      ( add-functional-vec-Commutative-Ring n v2 v3))
  associative-add-functional-vec-Commutative-Ring =
    associative-add-functional-vec-Ring (ring-Commutative-Ring R)

  functional-vec-Commutative-Ring-Semigroup : ℕ → Semigroup l
  functional-vec-Commutative-Ring-Semigroup =
    functional-vec-Ring-Semigroup (ring-Commutative-Ring R)

  left-unit-law-add-functional-vec-Commutative-Ring :
    (n : ℕ) (v : functional-vec-Commutative-Ring R n) →
    add-functional-vec-Commutative-Ring n
      ( zero-functional-vec-Commutative-Ring R n) v ＝ v
  left-unit-law-add-functional-vec-Commutative-Ring =
    left-unit-law-add-functional-vec-Ring (ring-Commutative-Ring R)

  right-unit-law-add-functional-vec-Commutative-Ring :
    (n : ℕ) (v : functional-vec-Commutative-Ring R n) →
    add-functional-vec-Commutative-Ring n v
      ( zero-functional-vec-Commutative-Ring R n) ＝ v
  right-unit-law-add-functional-vec-Commutative-Ring =
    right-unit-law-add-functional-vec-Ring (ring-Commutative-Ring R)

  functional-vec-Commutative-Ring-Monoid : ℕ → Monoid l
  functional-vec-Commutative-Ring-Monoid =
    functional-vec-Ring-Monoid (ring-Commutative-Ring R)

  commutative-add-functional-vec-Commutative-Ring :
    (n : ℕ) (v w : functional-vec-Commutative-Ring R n) →
    add-functional-vec-Commutative-Ring n v w ＝
    add-functional-vec-Commutative-Ring n w v
  commutative-add-functional-vec-Commutative-Ring =
    commutative-add-functional-vec-Ring (ring-Commutative-Ring R)

  functional-vec-Commutative-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  functional-vec-Commutative-Ring-Commutative-Monoid =
    functional-vec-Ring-Commutative-Monoid (ring-Commutative-Ring R)
```
