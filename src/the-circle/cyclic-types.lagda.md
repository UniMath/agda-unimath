---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module the-circle.cyclic-types where

open import the-circle.infinite-cyclic-types public

Fin-Endo : ℕ → Endo lzero
pr1 (Fin-Endo k) = Fin k
pr2 (Fin-Endo k) = succ-Fin

Cyclic : (l : Level) → ℕ → UU (lsuc l)
Cyclic l zero-ℕ = Infinite-Cyclic l
Cyclic l (succ-ℕ k) = Σ (Endo l) (mere-equiv-Endo (Fin-Endo (succ-ℕ k)))

Fin-Cyclic : (k : ℕ) → Cyclic lzero (succ-ℕ k)
pr1 (Fin-Cyclic k) = Fin-Endo (succ-ℕ k)
pr2 (Fin-Cyclic k) = refl-mere-equiv-Endo (Fin-Endo (succ-ℕ k))

module _
  {l : Level}
  where

  endo-Cyclic : (k : ℕ) → Cyclic l k → Endo l
  endo-Cyclic zero-ℕ = pr1
  endo-Cyclic (succ-ℕ k) = pr1
  
  type-Cyclic : (k : ℕ) → Cyclic l k → UU l
  type-Cyclic zero-ℕ = type-Endo ∘ endo-Cyclic zero-ℕ
  type-Cyclic (succ-ℕ k) = type-Endo ∘ endo-Cyclic (succ-ℕ k)
  
  endomorphism-Cyclic :
    (k : ℕ) (X : Cyclic l k) → type-Cyclic k X → type-Cyclic k X
  endomorphism-Cyclic zero-ℕ X = endomorphism-Endo (endo-Cyclic zero-ℕ X)
  endomorphism-Cyclic (succ-ℕ k) X =
    endomorphism-Endo (endo-Cyclic (succ-ℕ k) X)

```
