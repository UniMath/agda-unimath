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

Given a [monoid](group-theory.monoids.md) `M`, the type `vec n M` of
`n`-dimensional `M`-[vectors](linear-algebra.vectors.md) is a monoid given by
componentwise multiplication.

We use additive terminology for vectors, as is standard in linear algebra
contexts, despite using multiplicative terminology for monoids.

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

### The zero vector

#### The listed zero vector

```agda
module _
  {l : Level} (M : Monoid l)
  where

  zero-vec-Monoid : {n : ℕ} → vec-Monoid M n
  zero-vec-Monoid = constant-vec (unit-Monoid M)
```

#### The functional zero vector

```agda
module _
  {l : Level} (M : Monoid l)
  where

  zero-functional-vec-Monoid : (n : ℕ) → functional-vec-Monoid M n
  zero-functional-vec-Monoid n i = unit-Monoid M
```

### Pointwise addition of vectors on a monoid

#### Pointwise addition of listed vectors on a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  add-vec-Monoid :
    {n : ℕ} → vec-Monoid M n → vec-Monoid M n → vec-Monoid M n
  add-vec-Monoid = binary-map-vec (mul-Monoid M)

  associative-add-vec-Monoid :
    {n : ℕ} (v1 v2 v3 : vec-Monoid M n) →
    add-vec-Monoid (add-vec-Monoid v1 v2) v3 ＝
    add-vec-Monoid v1 (add-vec-Monoid v2 v3)
  associative-add-vec-Monoid empty-vec empty-vec empty-vec = refl
  associative-add-vec-Monoid (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-mul-Monoid M x y z)
      ( associative-add-vec-Monoid v1 v2 v3)

  vec-Monoid-Semigroup : ℕ → Semigroup l
  pr1 (vec-Monoid-Semigroup n) = vec-Set (set-Monoid M) n
  pr1 (pr2 (vec-Monoid-Semigroup n)) = add-vec-Monoid
  pr2 (pr2 (vec-Monoid-Semigroup n)) = associative-add-vec-Monoid

  left-unit-law-add-vec-Monoid :
    {n : ℕ} (v : vec-Monoid M n) →
    add-vec-Monoid (zero-vec-Monoid M) v ＝ v
  left-unit-law-add-vec-Monoid empty-vec = refl
  left-unit-law-add-vec-Monoid (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-mul-Monoid M x)
      ( left-unit-law-add-vec-Monoid v)

  right-unit-law-add-vec-Monoid :
    {n : ℕ} (v : vec-Monoid M n) →
    add-vec-Monoid v (zero-vec-Monoid M) ＝ v
  right-unit-law-add-vec-Monoid empty-vec = refl
  right-unit-law-add-vec-Monoid (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-mul-Monoid M x)
      ( right-unit-law-add-vec-Monoid v)

  vec-Monoid-Monoid : ℕ → Monoid l
  pr1 (vec-Monoid-Monoid n) = vec-Monoid-Semigroup n
  pr1 (pr2 (vec-Monoid-Monoid n)) = zero-vec-Monoid M
  pr1 (pr2 (pr2 (vec-Monoid-Monoid n))) = left-unit-law-add-vec-Monoid
  pr2 (pr2 (pr2 (vec-Monoid-Monoid n))) = right-unit-law-add-vec-Monoid
```

#### Pointwise addition of functional vectors on a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  add-functional-vec-Monoid :
    (n : ℕ) (v w : functional-vec-Monoid M n) → functional-vec-Monoid M n
  add-functional-vec-Monoid n = binary-map-functional-vec n (mul-Monoid M)

  associative-add-functional-vec-Monoid :
    (n : ℕ) (v1 v2 v3 : functional-vec-Monoid M n) →
    ( add-functional-vec-Monoid n (add-functional-vec-Monoid n v1 v2) v3) ＝
    ( add-functional-vec-Monoid n v1 (add-functional-vec-Monoid n v2 v3))
  associative-add-functional-vec-Monoid n v1 v2 v3 =
    eq-htpy (λ i → associative-mul-Monoid M (v1 i) (v2 i) (v3 i))

  functional-vec-Monoid-Semigroup : ℕ → Semigroup l
  pr1 (functional-vec-Monoid-Semigroup n) =
    functional-vec-Set (set-Monoid M) n
  pr1 (pr2 (functional-vec-Monoid-Semigroup n)) =
    add-functional-vec-Monoid n
  pr2 (pr2 (functional-vec-Monoid-Semigroup n)) =
    associative-add-functional-vec-Monoid n

  left-unit-law-add-functional-vec-Monoid :
    (n : ℕ) (v : functional-vec-Monoid M n) →
    add-functional-vec-Monoid n (zero-functional-vec-Monoid M n) v ＝ v
  left-unit-law-add-functional-vec-Monoid n v =
    eq-htpy (λ i → left-unit-law-mul-Monoid M (v i))

  right-unit-law-add-functional-vec-Monoid :
    (n : ℕ) (v : functional-vec-Monoid M n) →
    add-functional-vec-Monoid n v (zero-functional-vec-Monoid M n) ＝ v
  right-unit-law-add-functional-vec-Monoid n v =
    eq-htpy (λ i → right-unit-law-mul-Monoid M (v i))

  functional-vec-Monoid-Monoid : ℕ → Monoid l
  pr1 (functional-vec-Monoid-Monoid n) =
    functional-vec-Monoid-Semigroup n
  pr1 (pr2 (functional-vec-Monoid-Monoid n)) =
    zero-functional-vec-Monoid M n
  pr1 (pr2 (pr2 (functional-vec-Monoid-Monoid n))) =
    left-unit-law-add-functional-vec-Monoid n
  pr2 (pr2 (pr2 (functional-vec-Monoid-Monoid n))) =
    right-unit-law-add-functional-vec-Monoid n
```
