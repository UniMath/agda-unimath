# Tuples on commutative monoids

```agda
module linear-algebra.tuples-on-commutative-monoids where
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
open import linear-algebra.tuples-on-monoids

open import lists.tuples
```

</details>

## Idea

Given a [commutative monoid](group-theory.commutative-monoids.md) `M`, the type
`tuple n M` of `n`-[tuples](lists.tuples.md) of elements of `M` is a commutative
monoid given by componentwise addition.

We use additive terminology for tuples, as is standard in linear algebra
contexts, despite using multiplicative terminology for monoids.

## Definitions

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  tuple-Commutative-Monoid : ℕ → UU l
  tuple-Commutative-Monoid = tuple-Monoid (monoid-Commutative-Monoid M)

  head-tuple-Commutative-Monoid :
    {n : ℕ} → tuple-Commutative-Monoid (succ-ℕ n) → type-Commutative-Monoid M
  head-tuple-Commutative-Monoid =
    head-tuple-Monoid (monoid-Commutative-Monoid M)

  tail-tuple-Commutative-Monoid :
    {n : ℕ} → tuple-Commutative-Monoid (succ-ℕ n) → tuple-Commutative-Monoid n
  tail-tuple-Commutative-Monoid =
    tail-tuple-Monoid (monoid-Commutative-Monoid M)

  snoc-tuple-Commutative-Monoid :
    {n : ℕ} → tuple-Commutative-Monoid n → type-Commutative-Monoid M →
    tuple-Commutative-Monoid (succ-ℕ n)
  snoc-tuple-Commutative-Monoid =
    snoc-tuple-Monoid (monoid-Commutative-Monoid M)
```

### Tuple of zeros of a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  zero-tuple-Commutative-Monoid : {n : ℕ} → tuple-Commutative-Monoid M n
  zero-tuple-Commutative-Monoid = constant-tuple (unit-Commutative-Monoid M)
```

### Componentwise addition of tuples on a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  add-tuple-Commutative-Monoid :
    {n : ℕ} → tuple-Commutative-Monoid M n → tuple-Commutative-Monoid M n →
    tuple-Commutative-Monoid M n
  add-tuple-Commutative-Monoid =
    add-tuple-Monoid (monoid-Commutative-Monoid M)

  associative-add-tuple-Commutative-Monoid :
    {n : ℕ} (v1 v2 v3 : tuple-Commutative-Monoid M n) →
    add-tuple-Commutative-Monoid (add-tuple-Commutative-Monoid v1 v2) v3 ＝
    add-tuple-Commutative-Monoid v1 (add-tuple-Commutative-Monoid v2 v3)
  associative-add-tuple-Commutative-Monoid =
    associative-add-tuple-Monoid (monoid-Commutative-Monoid M)

  semigroup-tuple-Commutative-Monoid : ℕ → Semigroup l
  semigroup-tuple-Commutative-Monoid =
    semigroup-tuple-Monoid (monoid-Commutative-Monoid M)

  left-unit-law-add-tuple-Commutative-Monoid :
    {n : ℕ} (v : tuple-Commutative-Monoid M n) →
    add-tuple-Commutative-Monoid (zero-tuple-Commutative-Monoid M) v ＝ v
  left-unit-law-add-tuple-Commutative-Monoid =
    left-unit-law-add-tuple-Monoid (monoid-Commutative-Monoid M)

  right-unit-law-add-tuple-Commutative-Monoid :
    {n : ℕ} (v : tuple-Commutative-Monoid M n) →
    add-tuple-Commutative-Monoid v (zero-tuple-Commutative-Monoid M) ＝ v
  right-unit-law-add-tuple-Commutative-Monoid =
    right-unit-law-add-tuple-Monoid (monoid-Commutative-Monoid M)

  monoid-tuple-Commutative-Monoid : ℕ → Monoid l
  monoid-tuple-Commutative-Monoid =
    monoid-tuple-Monoid (monoid-Commutative-Monoid M)

  commutative-add-tuple-Commutative-Monoid :
    {n : ℕ} (v w : tuple-Commutative-Monoid M n) →
    add-tuple-Commutative-Monoid v w ＝ add-tuple-Commutative-Monoid w v
  commutative-add-tuple-Commutative-Monoid empty-tuple empty-tuple = refl
  commutative-add-tuple-Commutative-Monoid (x ∷ v1) (y ∷ v2) =
    ap-binary _∷_
      (commutative-mul-Commutative-Monoid M x y)
      (commutative-add-tuple-Commutative-Monoid v1 v2)

  commutative-monoid-tuple-Commutative-Monoid : ℕ → Commutative-Monoid l
  commutative-monoid-tuple-Commutative-Monoid n =
    monoid-tuple-Commutative-Monoid n ,
    commutative-add-tuple-Commutative-Monoid
```
