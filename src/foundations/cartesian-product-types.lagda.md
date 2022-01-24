---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.cartesian-product-types where

open import foundations.empty-type using (is-empty)
open import foundations.levels using (Level; UU; _⊔_)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
```

## Cartesian products

```agda
prod : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prod A B = Σ A (λ a → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → prod A B
pair' = pair

_×_ :  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = prod A B
```
