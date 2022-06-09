# The universal property of coproduct types

```agda
{-# OPTIONS --without-K --exact-split #-}


module univalent-combinatorics.universal-property-coproduct-species-m where



open import foundation.cartesian-product-types using (_×_; pair')
open import foundation.coproduct-types using (coprod; inl; inr; ind-coprod)
open import foundation.dependent-pair-types using
  ( Σ; pair; pr1; pr2; ind-Σ)
open import foundation.equality-cartesian-product-types using
  ( eq-pair)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; is-equiv-is-equiv-precomp;
    is-equiv-right-factor'; is-equiv-comp; is-equiv-precomp-is-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; precomp)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels

open import univalent-combinatorics.species 
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.coproducts-species
open import univalent-combinatorics.finite-types
```

## Idea

The universal property and dependent universal property of coproduct types characterize maps and dependent functions out of coproduct types.

```agda
module _
  {l1 l2 : Level} {A : species l1} {B : species l2}
  where

  ev-inl-inr :
    {l3 : Level}(H : species l3) (P : (species-coprod A B) →ˢ l2) →
    ((t : species-coprod A B) → (P t)) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

  abstract
    dependent-universal-property-coprod :
      {l3 : Level} (P : coprod A B → species l3) → is-equiv (ev-inl-inr P)
    dependent-universal-property-coprod P =
      is-equiv-has-inverse
        ( λ p → ind-coprod P (pr1 p) (pr2 p))
        ( ind-Σ (λ f g → eq-pair refl refl))
        ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → species l3) →
    ((x : coprod A B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coprod P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coprod P) =
    dependent-universal-property-coprod P

  abstract
    universal-property-coprod :
      {l3 : Level} (X : species l3) →
      is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
    universal-property-coprod X = dependent-universal-property-coprod (λ t → X)
  
  equiv-universal-property-coprod :
    {l3 : Level} (X : species l3) →
    (coprod A B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ t → X)

```

 