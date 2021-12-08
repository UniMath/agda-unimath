---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.sheargroups where

open import groups.abstract-groups public

Sheargroup : (l : Level) → UU (lsuc l)
Sheargroup l =
  Σ ( UU-Set l)
    ( λ X →
      Σ ( type-Set X)
        ( λ e →
          Σ (type-Set X → type-Set X → type-Set X)
            ( λ m →
              ( (x : type-Set X) → Id (m e x) x) ×
              ( ( (x : type-Set X) → Id (m x x) e) ×
                ( (x y z : type-Set X) →
                  Id (m x (m y z)) (m (m (m x (m y e)) e) z))))))

```
