---
title: Furstenberg groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.furstenberg-groups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.propositional-truncations using (type-trunc-Prop)
open import foundation.sets using (Set; type-Set)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Definition

```agda
Furstenberg-Group : (l : Level) → UU (lsuc l)
Furstenberg-Group l =
  Σ ( Set l)
    ( λ X →
      ( type-trunc-Prop (type-Set X)) ×
      ( Σ ( type-Set X → type-Set X → type-Set X)
          ( λ μ →
            ( (x y z : type-Set X) → Id (μ (μ x z) (μ y z)) (μ x y)) ×
            ( Σ ( type-Set X → type-Set X → type-Set X)
                ( λ δ → (x y : type-Set X) → Id (μ x (δ x y)) y)))))

```
