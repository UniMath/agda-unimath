---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.cartesian-product-types where

open import foundations.levels using (Level; UU; _⊔_)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2) public

-- The dependent-pair-types module is opened publicly, because if one imports
-- the module cartesian-product-types, one may reasonably expect pair, pr1, and
-- pr2 to be there.
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

map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
pr1 (map-prod f g (pair a b)) = f a
pr2 (map-prod f g (pair a b)) = g b
```
