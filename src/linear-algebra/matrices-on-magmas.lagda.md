# Matrices on magmas

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices-on-magmas where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.functoriality-vectors using (map-binary-vec)
open import linear-algebra.matrices using (Mat)
open import linear-algebra.vectors-on-magmas using (mul-vec-Magma)

open import wild-algebra.magmas using (Magma; type-Magma; mul-Magma)
```

## Idea

If `M` is a magma`, then the type of matrices on `M` is a magma.

## Definition

## Operations on matrices

We take the binary operations in K as arguments.

For vector-matrix and matrix-matrix multiplication we also need a zero element, assumed to be the additive identity in K.

```agda
module _
  {l : Level} (M : Magma l)
  where
  
  type-Mat-Magma : ℕ → ℕ → UU l
  type-Mat-Magma = Mat (type-Magma M)
  
  pointwise-mul-Mat-Magma :
    {m n : ℕ} → type-Mat-Magma m n → type-Mat-Magma m n → type-Mat-Magma m n
  pointwise-mul-Mat-Magma = map-binary-vec (mul-vec-Magma M)
  
  Mat-Magma : ℕ → ℕ → Magma l
  pr1 (Mat-Magma m n) = type-Mat-Magma m n
  pr2 (Mat-Magma m n) = pointwise-mul-Mat-Magma
```

## Properties

```agda
module _
  {l : Level} (M : Magma l)
  where
  
{-TODO:
add-transpose :
  {l : Level} → {K : UU l} → {m n : ℕ} →
  {addK : K → K → K} →
  (a b : Mat K m n) →
  Id (transpose (add-Mat addK a b)) (add-Mat addK (transpose a) (transpose b))
add-transpose {n = zero-ℕ} a b = refl
add-transpose {n = succ-ℕ _}{addK} empty-vec empty-vec =
  ap-binary _∷_ refl (add-transpose {addK = addK} empty-vec empty-vec)
add-transpose {n = succ-ℕ _}{addK} (a ∷ as) (b ∷ bs) =
  ap-binary _∷_ (lemma-first-row a b as bs) (lemma-rest a b as bs)
  where
  lemma-first-row :
    {l : Level} → {K : UU l} → {m n : ℕ} →
    {addK : K → K → K} →
    (a' b' : vec K (succ-ℕ n)) → (as' bs' : Mat K m (succ-ℕ n)) →
    Id (map-vec head (add-Mat addK (a' ∷ as') (b' ∷ bs')))
       (add-vec addK (map-vec head (a' ∷ as')) (map-vec head (b' ∷ bs')))
  lemma-first-row {m = zero-ℕ} {n = n} {addK = addK'} (x ∷ a') (y ∷ b') empty-vec empty-vec = refl
  lemma-first-row {m = m} {n = n} {addK = addK'} (x ∷ a') (y ∷ b') (as' ∷ ass') (bs' ∷ bss') =
    ap-binary _∷_
      (ap head {y = addK' x y ∷ add-vec addK' a' b'} refl)
      (lemma-first-row {addK = addK'} as' bs' ass' bss')

  lemma-rest :
    {l : Level} → {K : UU l} → {m n : ℕ} →
    {addK : K → K → K} →
    (a' b' : vec K (succ-ℕ n)) → (as' bs' : Mat K m (succ-ℕ n)) →
    Id (transpose (tail (add-vec addK a' b') ∷ map-vec tail (add-Mat addK as' bs')))
       (add-Mat addK (transpose (tail a' ∷ map-vec tail as'))
                     (transpose (tail b' ∷ map-vec tail bs')))
  lemma-rest {m = zero-ℕ} {n = zero-ℕ} a' b' empty-vec empty-vec = refl
  lemma-rest {m = .zero-ℕ} {n = succ-ℕ n} (x ∷ a') (x₁ ∷ b') empty-vec empty-vec = {!!}
  lemma-rest {m = .(succ-ℕ _)} {n = zero-ℕ} (x ∷ a') (x₁ ∷ b') (as' ∷ as'') (bs' ∷ bs'') = {!!}
  lemma-rest {m = .(succ-ℕ _)} {n = succ-ℕ n} (x ∷ a') (x₁ ∷ b') (as' ∷ as'') (bs' ∷ bs'') = {!!}
-}
```
