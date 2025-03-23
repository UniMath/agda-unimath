# Vectors on monoids

```agda
module linear-algebra.vectors-on-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors
```

</details>

## Idea

Given a [monoid](group-theory.monoids.md) `M`, the type `vec n M` of `n`-dimensional
`M`-[vectors](linear-algebra.vectors.md) is a monoid given by componentwise multiplication.

## Definitions

### Listed vectors on monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  vec-Monoid : ℕ → UU l
  vec-Monoid = vec (type-Monoid M)

  head-vec-Monoid : {n : ℕ} → vec-Monoid (succ-ℕ n) → type-Monoid M
  head-vec-Monoid v = head-vec v

  tail-vec-Monoid : {n : ℕ} → vec-Monoid (succ-ℕ n) → vec-Monoid n
  tail-vec-Monoid v = tail-vec v

  snoc-vec-Monoid :
    {n : ℕ} → vec-Monoid n → type-Monoid M → vec-Monoid (succ-ℕ n)
  snoc-vec-Monoid v r = snoc-vec v r
```

### Functional vectors on monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  functional-vec-Monoid : ℕ → UU l
  functional-vec-Monoid = functional-vec (type-Monoid M)

  head-functional-vec-Monoid :
    (n : ℕ) → functional-vec-Monoid (succ-ℕ n) → type-Monoid M
  head-functional-vec-Monoid n v = head-functional-vec n v

  tail-functional-vec-Monoid :
    (n : ℕ) → functional-vec-Monoid (succ-ℕ n) → functional-vec-Monoid n
  tail-functional-vec-Monoid = tail-functional-vec

  cons-functional-vec-Monoid :
    (n : ℕ) → type-Monoid M →
    functional-vec-Monoid n → functional-vec-Monoid (succ-ℕ n)
  cons-functional-vec-Monoid = cons-functional-vec

  snoc-functional-vec-Monoid :
    (n : ℕ) → functional-vec-Monoid n → type-Monoid M →
    functional-vec-Monoid (succ-ℕ n)
  snoc-functional-vec-Monoid = snoc-functional-vec
```

### Zero vector on a monoid

#### The unit listed vector

```agda
module _
  {l : Level} (M : Monoid l)
  where

  unit-vec-Monoid : {n : ℕ} → vec-Monoid M n
  unit-vec-Monoid = constant-vec (unit-Monoid M)
```

#### The unit functional vector

```agda
module _
  {l : Level} (M : Monoid l)
  where

  unit-functional-vec-Monoid : (n : ℕ) → functional-vec-Monoid M n
  unit-functional-vec-Monoid n i = unit-Monoid M
```

### Pointwise multiplication of vectors on a monoid

#### Pointwise multiplication of listed vectors on a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-vec-Monoid :
    {n : ℕ} → vec-Monoid M n → vec-Monoid M n → vec-Monoid M n
  mul-vec-Monoid = binary-map-vec (mul-Monoid M)

  associative-mul-vec-Monoid :
    {n : ℕ} (v1 v2 v3 : vec-Monoid M n) →
    mul-vec-Monoid (mul-vec-Monoid v1 v2) v3 ＝
    mul-vec-Monoid v1 (mul-vec-Monoid v2 v3)
  associative-mul-vec-Monoid empty-vec empty-vec empty-vec = refl
  associative-mul-vec-Monoid (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-mul-Monoid M x y z)
      ( associative-mul-vec-Monoid v1 v2 v3)

  vec-Monoid-Semigroup : ℕ → Semigroup l
  pr1 (vec-Monoid-Semigroup n) = vec-Set (set-Monoid M) n
  pr1 (pr2 (vec-Monoid-Semigroup n)) = mul-vec-Monoid
  pr2 (pr2 (vec-Monoid-Semigroup n)) = associative-mul-vec-Monoid

  left-unit-law-mul-vec-Monoid :
    {n : ℕ} (v : vec-Monoid M n) →
    mul-vec-Monoid (unit-vec-Monoid M) v ＝ v
  left-unit-law-mul-vec-Monoid empty-vec = refl
  left-unit-law-mul-vec-Monoid (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-mul-Monoid M x)
      ( left-unit-law-mul-vec-Monoid v)

  right-unit-law-mul-vec-Monoid :
    {n : ℕ} (v : vec-Monoid M n) →
    mul-vec-Monoid v (unit-vec-Monoid M) ＝ v
  right-unit-law-mul-vec-Monoid empty-vec = refl
  right-unit-law-mul-vec-Monoid (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-mul-Monoid M x)
      ( right-unit-law-mul-vec-Monoid v)

  vec-Monoid-Monoid : ℕ → Monoid l
  pr1 (vec-Monoid-Monoid n) = vec-Monoid-Semigroup n
  pr1 (pr2 (vec-Monoid-Monoid n)) = unit-vec-Monoid M
  pr1 (pr2 (pr2 (vec-Monoid-Monoid n))) = left-unit-law-mul-vec-Monoid
  pr2 (pr2 (pr2 (vec-Monoid-Monoid n))) = right-unit-law-mul-vec-Monoid
```

#### Pointwise addition of functional vectors on a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-functional-vec-Monoid :
    (n : ℕ) (v w : functional-vec-Monoid M n) → functional-vec-Monoid M n
  mul-functional-vec-Monoid n = binary-map-functional-vec n (mul-Monoid M)

  associative-mul-functional-vec-Monoid :
    (n : ℕ) (v1 v2 v3 : functional-vec-Monoid M n) →
    ( mul-functional-vec-Monoid n (mul-functional-vec-Monoid n v1 v2) v3) ＝
    ( mul-functional-vec-Monoid n v1 (mul-functional-vec-Monoid n v2 v3))
  associative-mul-functional-vec-Monoid n v1 v2 v3 =
    eq-htpy (λ i → associative-mul-Monoid M (v1 i) (v2 i) (v3 i))

  functional-vec-Monoid-Semigroup : ℕ → Semigroup l
  pr1 (functional-vec-Monoid-Semigroup n) =
    functional-vec-Set (set-Monoid M) n
  pr1 (pr2 (functional-vec-Monoid-Semigroup n)) =
    mul-functional-vec-Monoid n
  pr2 (pr2 (functional-vec-Monoid-Semigroup n)) =
    associative-mul-functional-vec-Monoid n

  left-unit-law-mul-functional-vec-Monoid :
    (n : ℕ) (v : functional-vec-Monoid M n) →
    mul-functional-vec-Monoid n (unit-functional-vec-Monoid M n) v ＝ v
  left-unit-law-mul-functional-vec-Monoid n v =
    eq-htpy (λ i → left-unit-law-mul-Monoid M (v i))

  right-unit-law-mul-functional-vec-Monoid :
    (n : ℕ) (v : functional-vec-Monoid M n) →
    mul-functional-vec-Monoid n v (unit-functional-vec-Monoid M n) ＝ v
  right-unit-law-mul-functional-vec-Monoid n v =
    eq-htpy (λ i → right-unit-law-mul-Monoid M (v i))

  functional-vec-Monoid-Monoid : ℕ → Monoid l
  pr1 (functional-vec-Monoid-Monoid n) =
    functional-vec-Monoid-Semigroup n
  pr1 (pr2 (functional-vec-Monoid-Monoid n)) =
    unit-functional-vec-Monoid M n
  pr1 (pr2 (pr2 (functional-vec-Monoid-Monoid n))) =
    left-unit-law-mul-functional-vec-Monoid n
  pr2 (pr2 (pr2 (functional-vec-Monoid-Monoid n))) =
    right-unit-law-mul-functional-vec-Monoid n
```
