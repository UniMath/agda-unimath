---
title: Sheargroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.sheargroups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.sets using (Set; type-Set)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Definition

```agda
Sheargroup : (l : Level) → UU (lsuc l)
Sheargroup l =
  Σ ( Set l)
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
