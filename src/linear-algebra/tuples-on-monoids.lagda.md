# Tuples on monoids

```agda
module linear-algebra.tuples-on-monoids where
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

open import linear-algebra.constant-tuples

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

Given a [monoid](group-theory.monoids.md) `M`, the type `tuple n M` of
`n`-[tuples](lists.tuples.md) of elements of `M` is a monoid given by
componentwise multiplication.

We use additive terminology for tuples, as is standard in linear algebra
contexts, despite using multiplicative terminology for monoids.

## Definitions

```agda
module _
  {l : Level} (M : Monoid l)
  where

  tuple-Monoid : ℕ → UU l
  tuple-Monoid = tuple (type-Monoid M)

  head-tuple-Monoid : {n : ℕ} → tuple-Monoid (succ-ℕ n) → type-Monoid M
  head-tuple-Monoid v = head-tuple v

  tail-tuple-Monoid : {n : ℕ} → tuple-Monoid (succ-ℕ n) → tuple-Monoid n
  tail-tuple-Monoid v = tail-tuple v

  snoc-tuple-Monoid :
    {n : ℕ} → tuple-Monoid n → type-Monoid M → tuple-Monoid (succ-ℕ n)
  snoc-tuple-Monoid v r = snoc-tuple v r
```

### The tuple of zeros

```agda
module _
  {l : Level} (M : Monoid l)
  where

  zero-tuple-Monoid : {n : ℕ} → tuple-Monoid M n
  zero-tuple-Monoid = constant-tuple (unit-Monoid M)
```

### Componentwise addition of tuples on a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  add-tuple-Monoid :
    {n : ℕ} → tuple-Monoid M n → tuple-Monoid M n → tuple-Monoid M n
  add-tuple-Monoid = binary-map-tuple (mul-Monoid M)

  associative-add-tuple-Monoid :
    {n : ℕ} (v1 v2 v3 : tuple-Monoid M n) →
    add-tuple-Monoid (add-tuple-Monoid v1 v2) v3 ＝
    add-tuple-Monoid v1 (add-tuple-Monoid v2 v3)
  associative-add-tuple-Monoid empty-tuple empty-tuple empty-tuple = refl
  associative-add-tuple-Monoid (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-mul-Monoid M x y z)
      ( associative-add-tuple-Monoid v1 v2 v3)

  semigroup-tuple-Monoid : ℕ → Semigroup l
  pr1 (semigroup-tuple-Monoid n) = tuple-Set (set-Monoid M) n
  pr1 (pr2 (semigroup-tuple-Monoid n)) = add-tuple-Monoid
  pr2 (pr2 (semigroup-tuple-Monoid n)) = associative-add-tuple-Monoid

  left-unit-law-add-tuple-Monoid :
    {n : ℕ} (v : tuple-Monoid M n) →
    add-tuple-Monoid (zero-tuple-Monoid M) v ＝ v
  left-unit-law-add-tuple-Monoid empty-tuple = refl
  left-unit-law-add-tuple-Monoid (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-mul-Monoid M x)
      ( left-unit-law-add-tuple-Monoid v)

  right-unit-law-add-tuple-Monoid :
    {n : ℕ} (v : tuple-Monoid M n) →
    add-tuple-Monoid v (zero-tuple-Monoid M) ＝ v
  right-unit-law-add-tuple-Monoid empty-tuple = refl
  right-unit-law-add-tuple-Monoid (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-mul-Monoid M x)
      ( right-unit-law-add-tuple-Monoid v)

  monoid-tuple-Monoid : ℕ → Monoid l
  pr1 (monoid-tuple-Monoid n) = semigroup-tuple-Monoid n
  pr1 (pr2 (monoid-tuple-Monoid n)) = zero-tuple-Monoid M
  pr1 (pr2 (pr2 (monoid-tuple-Monoid n))) = left-unit-law-add-tuple-Monoid
  pr2 (pr2 (pr2 (monoid-tuple-Monoid n))) = right-unit-law-add-tuple-Monoid
```
