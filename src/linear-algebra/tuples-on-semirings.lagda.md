# Tuples on semirings

```agda
module linear-algebra.tuples-on-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-commutative-monoids

open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.semirings
```

</details>

## Idea

Given a [semiring](ring-theory.semirings.md) `R`, the type `tuple n R` of
`R`-[tuples](lists.tuples.md) is a
[commutative monoid](group-theory.commutative-monoids.md) under addition.

## Definitions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  tuple-Semiring : ℕ → UU l
  tuple-Semiring = tuple (type-Semiring R)

  head-tuple-Semiring : {n : ℕ} → tuple-Semiring (succ-ℕ n) → type-Semiring R
  head-tuple-Semiring v = head-tuple v

  tail-tuple-Semiring : {n : ℕ} → tuple-Semiring (succ-ℕ n) → tuple-Semiring n
  tail-tuple-Semiring v = tail-tuple v

  snoc-tuple-Semiring :
    {n : ℕ} → tuple-Semiring n → type-Semiring R → tuple-Semiring (succ-ℕ n)
  snoc-tuple-Semiring v r = snoc-tuple v r
```

### The zero tuple in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-tuple-Semiring : {n : ℕ} → tuple-Semiring R n
  zero-tuple-Semiring = constant-tuple (zero-Semiring R)
```

### Pointwise addition of tuples in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-tuple-Semiring :
    {n : ℕ} → tuple-Semiring R n → tuple-Semiring R n → tuple-Semiring R n
  add-tuple-Semiring =
    add-tuple-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  associative-add-tuple-Semiring :
    {n : ℕ} (v1 v2 v3 : tuple-Semiring R n) →
    add-tuple-Semiring R (add-tuple-Semiring R v1 v2) v3 ＝
    add-tuple-Semiring R v1 (add-tuple-Semiring R v2 v3)
  associative-add-tuple-Semiring =
    associative-add-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring R (zero-tuple-Semiring R) v ＝ v
  left-unit-law-add-tuple-Semiring =
    left-unit-law-add-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring R v (zero-tuple-Semiring R) ＝ v
  right-unit-law-add-tuple-Semiring =
    right-unit-law-add-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commutative-add-tuple-Semiring :
    {n : ℕ} (v w : tuple-Semiring R n) →
    add-tuple-Semiring R v w ＝ add-tuple-Semiring R w v
  commutative-add-tuple-Semiring =
    commutative-add-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  semigroup-tuple-Semiring : ℕ → Semigroup l
  semigroup-tuple-Semiring =
    semigroup-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  monoid-tuple-Semiring : ℕ → Monoid l
  monoid-tuple-Semiring =
    monoid-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  commutative-monoid-tuple-Semiring : ℕ → Commutative-Monoid l
  commutative-monoid-tuple-Semiring =
    commutative-monoid-tuple-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```
