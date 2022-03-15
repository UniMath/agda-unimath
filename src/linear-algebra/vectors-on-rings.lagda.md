# Vectors on rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-rings where
```

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module

## Properties

## Operations on vectors

 - scalar-vector multiplication
 - vector-vector addition
 - scalar/dot/inner product

```agda
scalar-product :
  {l : Level} {A : UU l} {n : ℕ} → (A → A → A) → (A → A → A) → A →
  vec A n → vec A n → A
scalar-product _ _ zeroK empty-vec empty-vec = zeroK
scalar-product addK mulK zeroK (x ∷ xs) (y ∷ ys) = addK (mulK x y)
  (scalar-product addK mulK zeroK xs ys)
```

## Properties of scalar-vector multiplication
  - left distributive k(v1 + v2) = kv1 + kv2

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {mulK : K → K → K}
  {zero : K}
  where
  left-distributive-scalar-vector :
    {n : ℕ} →
    ((x y z : K) → Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z))) →
    (k : K) → (v1 v2 : vec K n) →
    Id (mul-scalar-vector mulK k (add-vec addK v1 v2))
       (add-vec addK (mul-scalar-vector mulK k v1) (mul-scalar-vector mulK k v2))
  left-distributive-scalar-vector _ _ empty-vec empty-vec = refl
  left-distributive-scalar-vector k-distr k (x ∷ xs) (y ∷ ys) =
    (ap (λ k' → k' ∷ mul-scalar-vector mulK k (add-vec addK xs ys)) (k-distr k x y))
      ∙ ap (_∷_ (addK (mulK k x) (mulK k y)))
           (left-distributive-scalar-vector k-distr k xs ys)
```
