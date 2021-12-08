---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.furstenberg-groups where

open import groups.abstract-groups public

Furstenberg-Group : (l : Level) → UU (lsuc l)
Furstenberg-Group l =
  Σ ( UU-Set l)
    ( λ X →
      ( type-trunc-Prop (type-Set X)) ×
      ( Σ ( type-Set X → type-Set X → type-Set X)
          ( λ μ →
            ( (x y z : type-Set X) → Id (μ (μ x z) (μ y z)) (μ x y)) ×
            ( Σ ( type-Set X → type-Set X → type-Set X)
                ( λ δ → (x y : type-Set X) → Id (μ x (δ x y)) y)))))

```
