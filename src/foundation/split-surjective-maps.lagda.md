---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.split-surjective-maps where

open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.levels using (UU; Level; _⊔_)
```

# Split surjective maps

```agda
is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-split-surjective {A = A} {B} f = (b : B) → Σ A (λ a → Id (f a) b)
```
