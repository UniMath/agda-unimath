# Matrices on commutative monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices-on-commutative-monoids.lagda.md
```

```agda
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {zero : K}
  where

  commutative-add-matrices :
    {n m : ℕ} →
    ((x y : K) → Id (addK x y) (addK y x)) →
    (a b : Mat K m n) → Id (add-Mat addK a b) (add-Mat addK b a)
  commutative-add-matrices _ empty-vec empty-vec = refl
  commutative-add-matrices addK-comm (a ∷ as) (b ∷ bs) =
    (ap (λ v → v ∷ (add-Mat _ as bs)) (commutative-add-vectors {zero = zero} addK-comm a b))
      ∙ ap (_∷_ (add-vec _ b a)) (commutative-add-matrices addK-comm as bs)
```

