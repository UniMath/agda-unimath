# Vectors on monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-monoids where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.identity-types using (Id; refl; ap; _∙_)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.diagonal-vectors using (diagonal-vec)
open import linear-algebra.vectors using (vec; empty-vec; _∷_)
open import linear-algebra.vectors-on-magmas using
  ( type-vec-Magma; mul-vec-Magma; vec-Magma)

open import wild-algebra.magmas using (Magma; type-Magma; mul-Magma)
```

## Idea

Given a monoid `M`, the type `vec n M` is again a monoid.

## Properties

```agda
module _
  {l : Level} (M : Magma l) {zero : type-Magma M}
  where
  
  left-unit-add-vectors :
    {n : ℕ} →
    ((x : type-Magma M) → Id (mul-Magma M zero x) x) →
    (v : type-vec-Magma M n) → Id (mul-vec-Magma M (diagonal-vec zero) v) v
  left-unit-add-vectors _ empty-vec = refl
  left-unit-add-vectors addK-lUnit (x ∷ xs) =
    (ap (λ k → k ∷ mul-vec-Magma M (diagonal-vec zero) xs) (addK-lUnit x))
      ∙ ap (λ v → x ∷ v) (left-unit-add-vectors addK-lUnit xs)

  right-unit-add-vectors :
    {n : ℕ} →
    ((x : type-Magma M) → Id (mul-Magma M x zero) x) →
    (v : vec (type-Magma M) n) → Id (mul-vec-Magma M v (diagonal-vec zero)) v
  right-unit-add-vectors _ empty-vec = refl
  right-unit-add-vectors addK-rUnit (x ∷ xs) =
    (ap (λ k → k ∷ mul-vec-Magma M xs (diagonal-vec zero)) (addK-rUnit x))
      ∙ ap (λ v → x ∷ v) (right-unit-add-vectors addK-rUnit xs)

  associative-add-vectors :
    {n : ℕ} →
    ((x y z : type-Magma M) → Id (mul-Magma M x (mul-Magma M y z)) (mul-Magma M (mul-Magma M x y) z)) →
    (a b c : type-vec-Magma M n) →
    Id (mul-vec-Magma M a (mul-vec-Magma M b c)) (mul-vec-Magma M (mul-vec-Magma M a b) c)
  associative-add-vectors _ empty-vec empty-vec empty-vec = refl
  associative-add-vectors addK-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    ap (λ k → k ∷ (mul-vec-Magma M xs (mul-vec-Magma M ys zs))) (addK-assoc x y z)
      ∙ ap (_∷_ (mul-Magma M (mul-Magma M x y) z)) (associative-add-vectors addK-assoc xs ys zs)
```
