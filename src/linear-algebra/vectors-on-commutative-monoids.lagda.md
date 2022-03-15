# Vectors on commutative monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-commutative-monoids where
```

## Idea

Given a commutative monoid `M`, the type `vec n M` is again a commutative monoid

## Properties

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {zero : K}
  where

  commutative-add-vectors :
    {n : ℕ} →
    ((x y : K) → Id (addK x y) (addK y x)) →
    (a b : vec K n) → Id (add-vec addK a b) (add-vec addK b a)
  commutative-add-vectors _ empty-vec empty-vec = refl
  commutative-add-vectors addK-comm (x ∷ a) (y ∷ b) =
    ap (λ k → k ∷ add-vec addK a b) (addK-comm x y)
    ∙ ap (_∷_ (addK y x)) (commutative-add-vectors addK-comm a b)
```
