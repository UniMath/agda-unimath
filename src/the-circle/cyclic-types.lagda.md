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

```
