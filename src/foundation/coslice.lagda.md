# Morphisms in the coslice category of types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.coslice where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-inv-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_; _·r_; _∙h_; refl-htpy)
open import foundation.identity-types using (Id)
open import foundation.retractions using (retr)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : X → A) (g : X → B)
  where

  hom-coslice = Σ (A → B) (λ h → (h ∘ f) ~ g)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  map-hom-coslice : hom-coslice f g → (A → B)
  map-hom-coslice = pr1

  triangle-hom-coslice :
    (h : hom-coslice f g) → ((map-hom-coslice h) ∘ f) ~ g
  triangle-hom-coslice = pr2
```

## Properties

### Characterizing the identity type of coslice morphisms

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  htpy-hom-coslice :
    (h k : hom-coslice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-coslice h k =
    Σ ( map-hom-coslice h ~ map-hom-coslice k)
      ( λ H →
        (triangle-hom-coslice h) ~ ((H ·r f) ∙h (triangle-hom-coslice k)))

  extensionality-hom-coslice :
    (h k : hom-coslice f g) → Id h k ≃ htpy-hom-coslice h k
  extensionality-hom-coslice (pair h H) =
    extensionality-Σ
      ( λ {h' : A → B} (H' : (h' ∘ f) ~ g) (K : h ~ h') → H ~ ((K ·r f) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-hom-coslice :
    (h k : hom-coslice f g) (H : map-hom-coslice h ~ map-hom-coslice k)
    (K : (triangle-hom-coslice h) ~ ((H ·r f) ∙h (triangle-hom-coslice k))) →
    Id h k
  eq-htpy-hom-coslice h k H K =
    map-inv-equiv (extensionality-hom-coslice h k) (pair H K)
```

### Characterizing the identity type of `retr f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  htpy-retr : retr f → retr f → UU (l1 ⊔ l2)
  htpy-retr = htpy-hom-coslice

  extensionality-retr : (g h : retr f) → Id g h ≃ htpy-retr g h
  extensionality-retr g h = extensionality-hom-coslice g h

  eq-htpy-retr :
    ( g h : retr f) (H : pr1 g ~ pr1 h) (K : (pr2 g) ~ ((H ·r f) ∙h pr2 h)) →
    Id g h
  eq-htpy-retr g h = eq-htpy-hom-coslice g h 
```
