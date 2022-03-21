## Matrices on wild monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices-on-monoids where

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.matrices
open import linear-algebra.matrices-on-magmas

open import wild-algebra.wild-monoids
```

```agda
module _
  {l : Level} (M : Wild-Monoid l)
  where

--   associative-mul-Mat-Monoid :
--     {n m : ℕ} →
--     (A B C : Mat K m n) →
--     Id (add-Mat addK a (add-Mat addK b c)) (add-Mat addK (add-Mat addK a b) c)
--   associative-add-matrices _ empty-vec empty-vec empty-vec = refl
--   associative-add-matrices addK-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
--     (ap (λ v → v ∷ add-Mat _ xs (add-Mat _ ys zs)) (associative-add-vectors {zero = zero} addK-assoc x y z))
--       ∙ ap (_∷_ (add-vec _ (add-vec _ x y) z)) (associative-add-matrices addK-assoc xs ys zs)
-- ```
