---
title: Functions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functions where

open import foundation-core.functions public

open import foundation.identity-types using (_＝_)
open import foundation.universe-levels using (Level; UU)
```

Definition of the type of Commutiative Squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f-left : A → B) (f-bottom : B → D) (f-top : A → C) (f-right : C → D)
  where
  
  square-function-htpy : (x : A) → UU l4
  square-function-htpy x = ((f-bottom ∘ f-left) x) ＝ ((f-right ∘ f-top) x)
```
