---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.equivalences where

open import foundations.cartesian-product-types using (_×_)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.functions using (id; _∘_)
open import foundations.homotopies using
  ( _~_; refl-htpy; _∙h_; inv-htpy; _·r_; _·l_)
open import foundations.identity-types using (_∙_; inv; ap)
open import foundations.injective-maps using (is-injective)
open import foundations.levels using (Level; UU; _⊔_)
```

# Equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  sec : (f : A → B) → UU (l1 ⊔ l2)
  sec f = Σ (B → A) (λ g → (f ∘ g) ~ id)

  retr : (f : A → B) → UU (l1 ⊔ l2)
  retr f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  section-retract-of : A retract-of B → A → B
  section-retract-of = pr1

  retr-section-retract-of : (R : A retract-of B) → retr (section-retract-of R)
  retr-section-retract-of = pr2

  retraction-retract-of : (A retract-of B) → B → A
  retraction-retract-of R = pr1 (retr-section-retract-of R)

  is-retr-retraction-retract-of :
    (R : A retract-of B) →
    (retraction-retract-of R ∘ section-retract-of R) ~ id
  is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)

  -- Definition 9.2.1 (ii)
  
  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-equiv : (A ≃ B) → (A → B)
  map-equiv e = pr1 e

  is-equiv-map-equiv : (e : A ≃ B) → is-equiv (map-equiv e)
  is-equiv-map-equiv e = pr2 e
```

## The identity map is an equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy
  
  id-equiv : A ≃ A
  pr1 id-equiv = id
  pr2 id-equiv = is-equiv-id
```

## A map has an two-sided inverse if and only if it is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-inverse : (A → B) → UU (l1 ⊔ l2)
  has-inverse f = Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-has-inverse' : has-inverse f → is-equiv f
  pr1 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = H
  pr1 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = K

  is-equiv-has-inverse :
    (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
  is-equiv-has-inverse g H K =
    is-equiv-has-inverse' (pair g (pair H K))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  htpy-section-retraction : (H : is-equiv f) → ((pr1 (pr1 H))) ~ (pr1 (pr2 H))
  htpy-section-retraction (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

  has-inverse-is-equiv : is-equiv f → has-inverse f
  pr1 (has-inverse-is-equiv  (pair (pair g G) (pair h H))) = g
  pr1 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) = G
  pr2 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) =
    (((inv-htpy (H ·r g)) ∙h (h ·l G)) ·r f) ∙h H

  map-inv-is-equiv : is-equiv f → B → A
  map-inv-is-equiv H = pr1 (has-inverse-is-equiv H)

  issec-map-inv-is-equiv' :
    (H : is-equiv f) → (f ∘ (map-inv-is-equiv H)) ~ id
  issec-map-inv-is-equiv' H = pr1 (pr2 (has-inverse-is-equiv H))

  isretr-map-inv-is-equiv' :
    (H : is-equiv f) → ((map-inv-is-equiv H) ∘ f) ~ id
  isretr-map-inv-is-equiv' H = pr2 (pr2 (has-inverse-is-equiv H))

  is-equiv-map-inv-is-equiv : (H : is-equiv f) → is-equiv (map-inv-is-equiv H)
  is-equiv-map-inv-is-equiv H =
    is-equiv-has-inverse f
      ( isretr-map-inv-is-equiv' H)
      ( issec-map-inv-is-equiv' H)
```

## The inverse of an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv' : (B → A)
  map-inv-equiv' = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv' : (map-equiv e ∘ map-inv-equiv') ~ id
  issec-map-inv-equiv' = issec-map-inv-is-equiv' (is-equiv-map-equiv e)

  isretr-map-inv-equiv' : (map-inv-equiv' ∘ map-equiv e) ~ id
  isretr-map-inv-equiv' = isretr-map-inv-is-equiv' (is-equiv-map-equiv e)

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv'
  is-equiv-map-inv-equiv = is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

  inv-equiv : (B ≃ A)
  pr1 inv-equiv = map-inv-equiv'
  pr2 inv-equiv = is-equiv-map-inv-equiv
```

## Equivalences are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
    is-injective-is-equiv H {x} {y} p =
      ( inv (isretr-map-inv-is-equiv' H x)) ∙
      ( ( ap (map-inv-is-equiv H) p) ∙
        ( isretr-map-inv-is-equiv' H y))

  abstract
    is-injective-map-equiv : (e : A ≃ B) → is-injective (map-equiv e)
    is-injective-map-equiv (pair f H) = is-injective-is-equiv H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  abstract
    is-injective-map-inv-equiv : (e : A ≃ B) → is-injective (map-inv-equiv' e)
    is-injective-map-inv-equiv e =
      is-injective-is-equiv (is-equiv-map-inv-equiv e)

  is-equiv-is-injective : {f : A → B} → sec f → is-injective f → is-equiv f
  is-equiv-is-injective {f} (pair g G) H =
    is-equiv-has-inverse g G (λ x → H (G (f x)))
```
