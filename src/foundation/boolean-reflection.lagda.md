---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.boolean-reflection where

open import foundation.booleans using (bool; true; false; Eq-eq-bool)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.empty-type using (ex-falso)
open import foundation.identity-types using (Id; refl)
open import foundation.levels using (Level; UU)
```

# Boolean reflection

```agda
booleanization : {l : Level} {A : UU l} → is-decidable A → bool
booleanization (inl a) = true
booleanization (inr f) = false

inv-boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → A → Id (booleanization d) true
inv-boolean-reflection (inl a) x = refl
inv-boolean-reflection (inr f) x = ex-falso (f x)

boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → Id (booleanization d) true → A
boolean-reflection (inl a) p = a
boolean-reflection (inr f) p = ex-falso (Eq-eq-bool p)
```
