# Sections of type families

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.sections where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs using
  ( Π-total-fam; inv-distributive-Π-Σ; distributive-Π-Σ)
open import foundation.equivalences using
  ( is-equiv; is-equiv-right-factor; is-equiv-id; _≃_; is-equiv-left-factor;
    sec; _∘e_; id-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-Σ)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-right-swap-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-equiv-pr1-is-contr; is-contr-is-equiv-pr1; left-unit-law-Σ-is-contr)
open import foundation.universe-levels using (Level; UU)
open import foundation.weak-function-extensionality using (is-contr-Π)
```

## Idea

Any dependent function induces a section of the projection map

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section b a) = a
  pr2 (map-section b a) = b a

  htpy-map-section :
    (b : (x : A) → B x) → (pr1 ∘ map-section b) ~ id
  htpy-map-section b a = refl
```

## Properties

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-map-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → is-equiv (map-section b)
  is-equiv-map-section b C =
    is-equiv-right-factor
      ( id)
      ( pr1)
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-pr1-is-contr C)
      ( is-equiv-id)

  equiv-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → A ≃ Σ A B
  equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

  is-contr-fam-is-equiv-map-section :
    (b : (x : A) → B x) → is-equiv (map-section b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section b H =
    is-contr-is-equiv-pr1
      ( is-equiv-left-factor id pr1
        ( map-section b)
        ( htpy-map-section b)
        ( is-equiv-id)
        ( H))
```

### Any section of a type family is an injective map

```agda
is-injective-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section b)
is-injective-map-section b = ap pr1
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-sec-pr1 : sec (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-sec-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → Id y x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
```
