---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.functoriality-cartesian-product-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equality-cartesian-product-types using (eq-pair)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_; inv-htpy; _∙h_)
open import foundation.identity-types using (refl)
open import foundation.universe-levels using (Level; UU)
```

# Functoriality of cartesian product types

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-prod : (f : A → C) (g : B → D) → (A × B) → (C × D)
  pr1 (map-prod f g (pair a b)) = f a
  pr2 (map-prod f g (pair a b)) = g b

  map-prod-pr1 :
    (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
  map-prod-pr1 f g (pair a b) = refl

  map-prod-pr2 :
    (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
  map-prod-pr2 f g (pair a b) = refl

{- For our convenience we show that the functorial action of cartesian products
   preserves identity maps, compositions, homotopies, and equivalences. -}

map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl

map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k (pair a b) = refl

htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  abstract
    is-equiv-map-prod :
      (f : A → C) (g : B → D) →
      is-equiv f → is-equiv g → is-equiv (map-prod f g)
    pr1
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod sf sg
    pr2
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp sf sg f g)) ∙h
      ( (htpy-map-prod Sf Sg) ∙h map-prod-id)
    pr1
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod rf rg
    pr2
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp f g rf rg)) ∙h
      ( (htpy-map-prod Rf Rg) ∙h map-prod-id)

  equiv-prod : (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
  pr1 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) = map-prod f g
  pr2 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) =
    is-equiv-map-prod f g is-equiv-f is-equiv-g
```
