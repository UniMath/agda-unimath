---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.injective-maps where

open import foundation.dependent-pair-types using (pair)
open import foundation.embeddings using (is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation.equivalences using
  ( is-equiv; isretr-map-inv-is-equiv; map-inv-is-equiv; _≃_; map-equiv;
    map-inv-equiv; is-equiv-map-inv-equiv; sec; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap)
open import foundation.levels using (UU; Level; _⊔_)
open import foundation.propositional-maps using (is-prop-map; is-prop-map-is-emb)
open import foundation.propositions using (is-equiv-is-prop)
open import foundation.sets using (is-set; is-set-prop-in-id)
```

## Injective maps

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = ({x y : A} → Id (f x) (f y) → Id x y)

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

## Equivalences are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
    is-injective-is-equiv H {x} {y} p =
      ( inv (isretr-map-inv-is-equiv H x)) ∙
      ( ( ap (map-inv-is-equiv H) p) ∙
        ( isretr-map-inv-is-equiv H y))

  abstract
    is-injective-map-equiv : (e : A ≃ B) → is-injective (map-equiv e)
    is-injective-map-equiv (pair f H) = is-injective-is-equiv H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  abstract
    is-injective-map-inv-equiv : (e : A ≃ B) → is-injective (map-inv-equiv e)
    is-injective-map-inv-equiv e =
      is-injective-is-equiv (is-equiv-map-inv-equiv e)

  is-equiv-is-injective : {f : A → B} → sec f → is-injective f → is-equiv f
  is-equiv-is-injective {f} (pair g G) H =
    is-equiv-has-inverse g G (λ x → H (G (f x)))
```

## Any embedding is injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)
```

## Any injective map between sets is an embedding

```agda
abstract
  is-emb-is-injective' : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f)

  is-set-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-set A
  is-set-is-injective {f = f} H I =
    is-set-prop-in-id
      ( λ x y → Id (f x) (f y))
      ( λ x y → H (f x) (f y))
      ( λ x → refl)
      ( λ x y → I)

  is-emb-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-emb f
  is-emb-is-injective {f = f} H I =
    is-emb-is-injective' (is-set-is-injective H I) H f I

  is-prop-map-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-prop-map f
  is-prop-map-is-injective {f = f} H I =
    is-prop-map-is-emb (is-emb-is-injective H I)
```
