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

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-rings
```

</details>

## Idea

Tuples on a [commutative ring](commutative-algebra.commutative-rings.md) `R` are
[tuples](lists.tuples.md) on the underlying type of `R`. The commutative ring
structure on `R` induces further structure on the type of tuples on `R`.

## Definitions

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

### The zero tuple in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-tuple-Commutative-Ring : {n : ℕ} → tuple-Commutative-Ring R n
  zero-tuple-Commutative-Ring = constant-tuple (zero-Commutative-Ring R)
```

### Pointwise addition of tuples in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring R n → tuple-Commutative-Ring R n →
    tuple-Commutative-Ring R n
  add-tuple-Commutative-Ring =
    add-tuple-Ring (ring-Commutative-Ring R)
```

### Pointwise negation of tuples in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  neg-tuple-Commutative-Ring :
    {n : ℕ} → tuple-Commutative-Ring R n → tuple-Commutative-Ring R n
  neg-tuple-Commutative-Ring = neg-tuple-Ring (ring-Commutative-Ring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-add-tuple-Commutative-Ring :
    {n : ℕ} (v1 v2 v3 : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring R (add-tuple-Commutative-Ring R v1 v2) v3 ＝
    add-tuple-Commutative-Ring R v1 (add-tuple-Commutative-Ring R v2 v3)
  associative-add-tuple-Commutative-Ring =
    associative-add-tuple-Ring (ring-Commutative-Ring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring R (zero-tuple-Commutative-Ring R) v ＝ v
  left-unit-law-add-tuple-Commutative-Ring =
    left-unit-law-add-tuple-Ring (ring-Commutative-Ring R)

  right-unit-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring R v (zero-tuple-Commutative-Ring R) ＝ v
  right-unit-law-add-tuple-Commutative-Ring =
    right-unit-law-add-tuple-Ring (ring-Commutative-Ring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-add-tuple-Commutative-Ring :
    {n : ℕ} (v w : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring R v w ＝ add-tuple-Commutative-Ring R w v
  commutative-add-tuple-Commutative-Ring =
    commutative-add-tuple-Ring (ring-Commutative-Ring R)
```

### Inverse laws of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-inverse-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring
      ( R)
      ( neg-tuple-Commutative-Ring R v)
      ( v) ＝
      zero-tuple-Commutative-Ring R
  left-inverse-law-add-tuple-Commutative-Ring =
    left-inverse-law-add-tuple-Ring (ring-Commutative-Ring R)

  right-inverse-law-add-tuple-Commutative-Ring :
    {n : ℕ} (v : tuple-Commutative-Ring R n) →
    add-tuple-Commutative-Ring
      ( R)
      ( v)
      ( neg-tuple-Commutative-Ring R v) ＝
      zero-tuple-Commutative-Ring R
  right-inverse-law-add-tuple-Commutative-Ring =
    right-inverse-law-add-tuple-Ring (ring-Commutative-Ring R)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  tuple-Commutative-Ring-Semigroup : ℕ → Semigroup l
  tuple-Commutative-Ring-Semigroup =
    tuple-Ring-Semigroup (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Monoid : ℕ → Monoid l
  tuple-Commutative-Ring-Monoid =
    tuple-Ring-Monoid (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Commutative-Ring-Commutative-Monoid =
    tuple-Ring-Commutative-Monoid (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Group : ℕ → Group l
  tuple-Commutative-Ring-Group = tuple-Ring-Group (ring-Commutative-Ring R)

  tuple-Commutative-Ring-Ab : ℕ → Ab l
  tuple-Commutative-Ring-Ab = tuple-Ring-Ab (ring-Commutative-Ring R)
```
