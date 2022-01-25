---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.coproduct-types where

open import foundations.identity-types using (Id; refl)
open import foundations.injective-maps using (is-injective)
open import foundations.levels using (Level; lzero; _⊔_; UU)
open import foundations.negation using (¬)
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
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = coprod A B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = coprod A B} inr
  is-injective-inr refl = refl 

  neq-inl-inr : {x : A} {y : B} → ¬ (Id (inl x) (inr y))
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → ¬ (Id (inr x) (inl y))
  neq-inr-inl ()
```
