# Vectors on commutative monoids

```agda
module linear-algebra.vectors-on-commutative-monoids where
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

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors
open import linear-algebra.vectors-on-monoids
```

</details>

## Idea

Given a [commutative monoid](group-theory.commutative-monoids.md) `M`, the type
`vec n M` of `M`-[vectors](linear-algebra.vectors.md) is a commutative monoid.

## Definitions

### Listed vectors on commutative rings

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  vec-Commutative-Monoid : ℕ → UU l
  vec-Commutative-Monoid = vec-Monoid (monoid-Commutative-Monoid M)

  head-vec-Commutative-Monoid :
    {n : ℕ} → vec-Commutative-Monoid (succ-ℕ n) → type-Commutative-Monoid M
  head-vec-Commutative-Monoid = head-vec-Monoid (monoid-Commutative-Monoid M)

  tail-vec-Commutative-Monoid :
    {n : ℕ} → vec-Commutative-Monoid (succ-ℕ n) → vec-Commutative-Monoid n
  tail-vec-Commutative-Monoid = tail-vec-Monoid (monoid-Commutative-Monoid M)

  snoc-vec-Commutative-Monoid :
    {n : ℕ} → vec-Commutative-Monoid n → type-Commutative-Monoid M →
    vec-Commutative-Monoid (succ-ℕ n)
  snoc-vec-Commutative-Monoid = snoc-vec-Monoid (monoid-Commutative-Monoid M)
```

### Functional vectors on commutative rings

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  functional-vec-Commutative-Monoid : ℕ → UU l
  functional-vec-Commutative-Monoid =
    functional-vec-Monoid (monoid-Commutative-Monoid M)

  head-functional-vec-Commutative-Monoid :
    (n : ℕ) → functional-vec-Commutative-Monoid (succ-ℕ n) →
    type-Commutative-Monoid M
  head-functional-vec-Commutative-Monoid =
    head-functional-vec-Monoid (monoid-Commutative-Monoid M)

  tail-functional-vec-Commutative-Monoid :
    (n : ℕ) → functional-vec-Commutative-Monoid (succ-ℕ n) →
    functional-vec-Commutative-Monoid n
  tail-functional-vec-Commutative-Monoid =
    tail-functional-vec-Monoid (monoid-Commutative-Monoid M)

  cons-functional-vec-Commutative-Monoid :
    (n : ℕ) → type-Commutative-Monoid M →
    functional-vec-Commutative-Monoid n →
    functional-vec-Commutative-Monoid (succ-ℕ n)
  cons-functional-vec-Commutative-Monoid =
    cons-functional-vec-Monoid (monoid-Commutative-Monoid M)

  snoc-functional-vec-Commutative-Monoid :
    (n : ℕ) → functional-vec-Commutative-Monoid n →
    type-Commutative-Monoid M → functional-vec-Commutative-Monoid (succ-ℕ n)
  snoc-functional-vec-Commutative-Monoid =
    snoc-functional-vec-Monoid (monoid-Commutative-Monoid M)
```

### Unit vector on a commutative monoid

#### The unit listed vector

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  unit-vec-Commutative-Monoid : {n : ℕ} → vec-Commutative-Monoid M n
  unit-vec-Commutative-Monoid = constant-vec (unit-Commutative-Monoid M)
```

#### The unit functional vector

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  unit-functional-vec-Commutative-Monoid :
    (n : ℕ) → functional-vec-Commutative-Monoid M n
  unit-functional-vec-Commutative-Monoid n i = unit-Commutative-Monoid M
```

### Pointwise addition of vectors on a commutative monoid

#### Pointwise addition of listed vectors on a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  mul-vec-Commutative-Monoid :
    {n : ℕ} → vec-Commutative-Monoid M n → vec-Commutative-Monoid M n →
    vec-Commutative-Monoid M n
  mul-vec-Commutative-Monoid =
    mul-vec-Monoid (monoid-Commutative-Monoid M)

  associative-mul-vec-Commutative-Monoid :
    {n : ℕ} (v1 v2 v3 : vec-Commutative-Monoid M n) →
    mul-vec-Commutative-Monoid (mul-vec-Commutative-Monoid v1 v2) v3 ＝
    mul-vec-Commutative-Monoid v1 (mul-vec-Commutative-Monoid v2 v3)
  associative-mul-vec-Commutative-Monoid =
    associative-mul-vec-Monoid (monoid-Commutative-Monoid M)

  vec-Commutative-Monoid-Semigroup : ℕ → Semigroup l
  vec-Commutative-Monoid-Semigroup =
    vec-Monoid-Semigroup (monoid-Commutative-Monoid M)

  left-unit-law-mul-vec-Commutative-Monoid :
    {n : ℕ} (v : vec-Commutative-Monoid M n) →
    mul-vec-Commutative-Monoid (unit-vec-Commutative-Monoid M) v ＝ v
  left-unit-law-mul-vec-Commutative-Monoid =
    left-unit-law-mul-vec-Monoid (monoid-Commutative-Monoid M)

  right-unit-law-mul-vec-Commutative-Monoid :
    {n : ℕ} (v : vec-Commutative-Monoid M n) →
    mul-vec-Commutative-Monoid v (unit-vec-Commutative-Monoid M) ＝ v
  right-unit-law-mul-vec-Commutative-Monoid =
    right-unit-law-mul-vec-Monoid (monoid-Commutative-Monoid M)

  vec-Commutative-Monoid-Monoid : ℕ → Monoid l
  vec-Commutative-Monoid-Monoid =
    vec-Monoid-Monoid (monoid-Commutative-Monoid M)

  commutative-mul-vec-Commutative-Monoid :
    {n : ℕ} (v w : vec-Commutative-Monoid M n) →
    mul-vec-Commutative-Monoid v w ＝ mul-vec-Commutative-Monoid w v
  commutative-mul-vec-Commutative-Monoid empty-vec empty-vec = refl
  commutative-mul-vec-Commutative-Monoid (x ∷ v1) (y ∷ v2) =
    ap-binary _∷_
      (commutative-mul-Commutative-Monoid M x y)
      (commutative-mul-vec-Commutative-Monoid v1 v2)

  vec-Commutative-Monoid-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Commutative-Monoid-Commutative-Monoid n =
    vec-Commutative-Monoid-Monoid n ,
    commutative-mul-vec-Commutative-Monoid
```

#### Pointwise addition of functional vectors on a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  mul-functional-vec-Commutative-Monoid :
    (n : ℕ) (v w : functional-vec-Commutative-Monoid M n) →
    functional-vec-Commutative-Monoid M n
  mul-functional-vec-Commutative-Monoid =
    mul-functional-vec-Monoid (monoid-Commutative-Monoid M)

  associative-mul-functional-vec-Commutative-Monoid :
    (n : ℕ) (v1 v2 v3 : functional-vec-Commutative-Monoid M n) →
    ( mul-functional-vec-Commutative-Monoid n
      ( mul-functional-vec-Commutative-Monoid n v1 v2) v3) ＝
    ( mul-functional-vec-Commutative-Monoid n v1
      ( mul-functional-vec-Commutative-Monoid n v2 v3))
  associative-mul-functional-vec-Commutative-Monoid =
    associative-mul-functional-vec-Monoid (monoid-Commutative-Monoid M)

  functional-vec-Commutative-Monoid-Semigroup : ℕ → Semigroup l
  functional-vec-Commutative-Monoid-Semigroup =
    functional-vec-Monoid-Semigroup (monoid-Commutative-Monoid M)

  left-unit-law-mul-functional-vec-Commutative-Monoid :
    (n : ℕ) (v : functional-vec-Commutative-Monoid M n) →
    mul-functional-vec-Commutative-Monoid n
      ( unit-functional-vec-Commutative-Monoid M n) v ＝ v
  left-unit-law-mul-functional-vec-Commutative-Monoid =
    left-unit-law-mul-functional-vec-Monoid (monoid-Commutative-Monoid M)

  right-unit-law-mul-functional-vec-Commutative-Monoid :
    (n : ℕ) (v : functional-vec-Commutative-Monoid M n) →
    mul-functional-vec-Commutative-Monoid n v
      ( unit-functional-vec-Commutative-Monoid M n) ＝ v
  right-unit-law-mul-functional-vec-Commutative-Monoid =
    right-unit-law-mul-functional-vec-Monoid (monoid-Commutative-Monoid M)

  functional-vec-Commutative-Monoid-Monoid : ℕ → Monoid l
  functional-vec-Commutative-Monoid-Monoid =
    functional-vec-Monoid-Monoid (monoid-Commutative-Monoid M)

  commutative-mul-functional-vec-Commutative-Monoid :
    (n : ℕ) (v w : functional-vec-Commutative-Monoid M n) →
    mul-functional-vec-Commutative-Monoid n v w ＝
    mul-functional-vec-Commutative-Monoid n w v
  commutative-mul-functional-vec-Commutative-Monoid _ _ _ =
    eq-htpy (λ k → commutative-mul-Commutative-Monoid M _ _)

  functional-vec-Commutative-Monoid-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  functional-vec-Commutative-Monoid-Commutative-Monoid n =
    functional-vec-Commutative-Monoid-Monoid n ,
    commutative-mul-functional-vec-Commutative-Monoid n
```
