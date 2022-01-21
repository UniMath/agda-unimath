---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.coproduct-types where

open import foundations.levels using (Level; lzero; _⊔_; UU)
open import foundations.empty-type using (is-empty; ex-falso)
```

## Coproducts

```agda
data coprod {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x

map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → coprod A B → A
map-right-unit-law-coprod-is-empty A B nb (inl a) = a
map-right-unit-law-coprod-is-empty A B nb (inr b) = ex-falso (nb b)

map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → coprod A B → B
map-left-unit-law-coprod-is-empty A B na (inl a) = ex-falso (na a)
map-left-unit-law-coprod-is-empty A B na (inr b) = b
```
