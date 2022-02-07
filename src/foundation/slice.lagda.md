# Morphisms of the slice category of types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.slice where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; _∘e_; map-inv-equiv)
open import foundation.function-extensionality using
  ( equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.homotopies using
  ( _~_; refl-htpy; _∙h_; _·l_; right-unit-htpy; is-contr-total-htpy;
    equiv-concat-htpy)
open import foundation.identity-types using (Id; refl)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The slice of a category over an object X is the category of morphisms into X. A morphism in the slice from `f : A → X` to `g : B → X` consists of a function `h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these definitions for types.

## Definition

```agda
hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice {A = A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))

map-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → A → B
map-hom-slice f g h = pr1 h

triangle-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  f ~ (g ∘ (map-hom-slice f g h))
triangle-hom-slice f g h = pr2 h
```

## Properties

### We characterize the identity type of hom-slice

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( λ K →
        ( (triangle-hom-slice f g h) ∙h (g ·l K)) ~
        ( triangle-hom-slice f g h'))

  extensionality-hom-slice :
    (h h' : hom-slice f g) → Id h h' ≃ htpy-hom-slice h h'
  extensionality-hom-slice (pair h H) =
    extensionality-Σ
      ( λ {h'} H' (K : h ~ h') → (H ∙h (g ·l K)) ~ H')
      ( refl-htpy)
      ( right-unit-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-concat-htpy (right-unit-htpy) H' ∘e equiv-funext)

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → Id h h'
  eq-htpy-hom-slice h h' = map-inv-equiv (extensionality-hom-slice h h')
```
