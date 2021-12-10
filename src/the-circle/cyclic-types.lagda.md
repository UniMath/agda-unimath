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

Cyclic : (l : Level) → ℕ → UU (lsuc lzero)
Cyclic l zero-ℕ = Infinite-Cyclic
Cyclic l (succ-ℕ k) =
  Σ (Endo lzero) (λ X → mere-equiv-Endo (Fin-Endo (succ-ℕ k)) X)

Fin-Cyclic : (k : ℕ) → Cyclic lzero k
Fin-Cyclic zero-ℕ = {!ℤ-Infinite-Cyclic!}
Fin-Cyclic (succ-ℕ k) = {!!}

```
