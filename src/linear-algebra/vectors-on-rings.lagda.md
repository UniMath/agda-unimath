# Vectors on rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-rings where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.identity-types using (Id; refl; ap-binary)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.constant-vectors using (constant-vec)
open import linear-algebra.functoriality-vectors using
  ( map-binary-vec; htpy-vec)
open import linear-algebra.scalar-multiplication-vectors using (scalar-mul-vec)
open import linear-algebra.vectors using
  ( vec; empty-vec; _∷_; head-vec; tail-vec)

open import ring-theory.rings using
  ( Ring; type-Ring; add-Ring; zero-Ring; left-unit-law-add-Ring;
    right-unit-law-add-Ring)
```

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where
  
  vec-Ring : ℕ → UU l
  vec-Ring = vec (type-Ring R)

  head-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → type-Ring R
  head-vec-Ring v = head-vec v

  tail-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → vec-Ring n
  tail-vec-Ring v = tail-vec v
```

### Zero vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-vec-Ring : {n : ℕ} → vec-Ring R n
  zero-vec-Ring {n} = constant-vec (zero-Ring R)
```

### Pointwise addition of vectors on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n → vec-Ring R n
  add-vec-Ring = map-binary-vec (add-Ring R)

  left-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring (zero-vec-Ring R) v) v
  left-unit-law-add-vec-Ring empty-vec = refl
  left-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Ring R x)
      ( left-unit-law-add-vec-Ring v)

  right-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring v (zero-vec-Ring R)) v
  right-unit-law-add-vec-Ring empty-vec = refl
  right-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Ring R x)
      ( right-unit-law-add-vec-Ring v)
```

## Properties

## Operations on vectors

 - scalar-vector multiplication
 - vector-vector addition
 - scalar/dot/inner product

-- ```agda
-- scalar-product :
--   {l : Level} {A : UU l} {n : ℕ} → (A → A → A) → (A → A → A) → A →
--   vec A n → vec A n → A
-- scalar-product _ _ zeroK empty-vec empty-vec = zeroK
-- scalar-product addK mulK zeroK (x ∷ xs) (y ∷ ys) = addK (mulK x y)
--   (scalar-product addK mulK zeroK xs ys)
-- ```

-- ## Properties of scalar-vector multiplication
--   - left distributive k(v1 + v2) = kv1 + kv2

-- ```agda
-- module _
--   {l : Level}
--   {K : UU l}
--   {addK : K → K → K}
--   {mulK : K → K → K}
--   {zero : K}
--   where
--   left-distributive-scalar-vector :
--     {n : ℕ} →
--     ((x y z : K) → Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z))) →
--     (k : K) → (v1 v2 : vec K n) →
--     Id (scalar-mul-vec mulK k (add-vec addK v1 v2))
--        (add-vec addK (mul-scalar-vector mulK k v1) (mul-scalar-vector mulK k v2))
--   left-distributive-scalar-vector _ _ empty-vec empty-vec = refl
--   left-distributive-scalar-vector k-distr k (x ∷ xs) (y ∷ ys) =
--     (ap (λ k' → k' ∷ mul-scalar-vector mulK k (add-vec addK xs ys)) (k-distr k x y))
--       ∙ ap (_∷_ (addK (mulK k x) (mulK k y)))
--            (left-distributive-scalar-vector k-distr k xs ys)
-- ```
