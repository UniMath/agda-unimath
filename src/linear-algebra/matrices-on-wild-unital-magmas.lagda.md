# Matrices on wild unital magmas

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices-on-wild-unital-magmas where
```

## Properties

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {zero : K}
  where
  
  left-unit-add-matrices :
    {n m : ℕ} →
    ((x : K) → Id (addK zero x) x) →
    (v : Mat K m n) → Id (add-Mat addK (diagonal (diagonal zero)) v) v
  left-unit-add-matrices _ empty-vec = refl
  left-unit-add-matrices addK-lUnit (x ∷ xs) =
    (ap (λ v → v ∷ add-Mat addK (diagonal (diagonal zero)) xs) (left-unit-add-vectors addK-lUnit x))
      ∙ ap (λ m → x ∷ m) (left-unit-add-matrices addK-lUnit xs)

  right-unit-add-matrices :
    {n m : ℕ} →
    ((x : K) → Id (addK x zero) x) →
    (v : Mat K m n) → Id (add-Mat addK v (diagonal (diagonal zero))) v
  right-unit-add-matrices _ empty-vec = refl
  right-unit-add-matrices addK-lUnit (x ∷ xs) =
    (ap (λ v → v ∷ add-Mat addK xs (diagonal (diagonal zero))) (right-unit-add-vectors addK-lUnit x))
      ∙ ap (λ m → x ∷ m) (right-unit-add-matrices addK-lUnit xs)
```
