---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.injective-maps where

open import foundations.functions using (id; _∘_)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap)
open import foundations.levels using (UU; Level; _⊔_)
open import foundations.negation using (¬)
```

## Injective maps

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = ({x y : A} → Id (f x) (f y) → Id x y)

is-not-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-not-injective f = ¬ (is-injective f)

is-injective-id : {l1 : Level} {A : UU l1} → is-injective (id {A = A})
is-injective-id p = p

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  is-injective-is-injective-comp :
    (f : A → C) (g : B → C) (h : A → B) (H : (a : A) → Id (f a) (g (h a))) →
    is-injective f → is-injective h
  is-injective-is-injective-comp f g h H is-inj-f {x} {x'} p =
    is-inj-f {x} {x'} ((H x) ∙ ((ap g p) ∙ (inv (H x'))))

  is-injective-comp :
    (f : A → C) (g : B → C) (h : A → B) (H : (a : A) → Id (f a) (g (h a))) →
    is-injective h → is-injective g → is-injective f
  is-injective-comp f g h H is-inj-h is-inj-g {x} {x'} p =
    is-inj-h (is-inj-g ((inv (H x)) ∙ (p ∙ (H x'))))

  is-injective-comp' :
    {g : B → C} {h : A → B} →
    is-injective h → is-injective g → is-injective (g ∘ h)
  is-injective-comp' {g} {h} H G =
    is-injective-comp (g ∘ h) g h (λ x → refl) H G
```
