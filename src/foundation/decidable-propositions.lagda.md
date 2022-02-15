# Decidable propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-propositions where

open import foundation.booleans using
  ( bool; true; false; is-set-bool; neq-false-true-bool)
open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (equiv-is-contr; eq-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-prop-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( equiv-is-empty; raise-empty-Prop; is-empty-raise-empty)
open import foundation.equivalences using
  ( _≃_; _∘e_; map-equiv; equiv-ap; is-equiv; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; ap; refl)
open import foundation.negation using (¬)
open import foundation.propositional-extensionality using
  ( is-contr-total-true-Prop; is-contr-total-false-Prop)
open import foundation.propositions using
  ( is-prop; UU-Prop; type-Prop; is-prop-type-Prop; is-prop-is-inhabited;
    is-prop-prod; is-prop-is-prop; is-proof-irrelevant-is-prop)
open import foundation.type-arithmetic-coproduct-types using
  ( left-distributive-Σ-coprod)
open import foundation.type-arithmetic-dependent-pair-types using
  ( inv-assoc-Σ)
open import foundation.unit-type using
  ( is-contr-unit; raise-unit-Prop; raise-star)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

A decidable proposition is a proposition that is decidable.

## Definition

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (UU l) is-decidable-prop

module _
  {l : Level} (P : decidable-Prop l)
  where

  prop-decidable-Prop : UU-Prop l
  pr1 prop-decidable-Prop = pr1 P
  pr2 prop-decidable-Prop = pr1 (pr2 P)

  type-decidable-Prop : UU l
  type-decidable-Prop = type-Prop prop-decidable-Prop

  abstract
    is-prop-type-decidable-Prop : is-prop type-decidable-Prop
    is-prop-type-decidable-Prop = is-prop-type-Prop prop-decidable-Prop

  is-decidable-type-decidable-Prop : is-decidable type-decidable-Prop
  is-decidable-type-decidable-Prop = pr2 (pr2 P)

  is-decidable-prop-type-decidable-Prop : is-decidable-prop type-decidable-Prop
  is-decidable-prop-type-decidable-Prop = pr2 P

  is-decidable-prop-decidable-Prop : UU-Prop l
  pr1 is-decidable-prop-decidable-Prop = is-decidable type-decidable-Prop
  pr2 is-decidable-prop-decidable-Prop =
    is-prop-is-decidable is-prop-type-decidable-Prop
```

## Properties

### Being a decidable proposition is a property

```agda
abstract
  is-prop-is-decidable-prop :
    {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
  is-prop-is-decidable-prop X =
    is-prop-is-inhabited
      ( λ H →
        is-prop-prod
          ( is-prop-is-prop X)
          ( is-prop-is-decidable (pr1 H)))
```

```agda
module _
  {l : Level}
  where
  
  split-decidable-Prop :
    decidable-Prop l ≃
    coprod (Σ (UU-Prop l) type-Prop) (Σ (UU-Prop l) (λ Q → ¬ (type-Prop Q)))
  split-decidable-Prop =
    ( left-distributive-Σ-coprod (UU-Prop l) (λ Q → pr1 Q) (λ Q → ¬ (pr1 Q))) ∘e
    ( inv-assoc-Σ (UU l) is-prop (λ X → is-decidable (pr1 X)))

  map-equiv-bool-decidable-Prop' :
    coprod (Σ (UU-Prop l) type-Prop) (Σ (UU-Prop l) (λ Q → ¬ (type-Prop Q))) →
    bool
  map-equiv-bool-decidable-Prop' (inl x) = true
  map-equiv-bool-decidable-Prop' (inr x) = false

  map-inv-equiv-bool-decidable-Prop' :
    bool →
    coprod (Σ (UU-Prop l) type-Prop) (Σ (UU-Prop l) (λ Q → ¬ (type-Prop Q)))
  map-inv-equiv-bool-decidable-Prop' true =
    inl (pair (raise-unit-Prop l) raise-star)
  map-inv-equiv-bool-decidable-Prop' false =
    inr (pair (raise-empty-Prop l) is-empty-raise-empty)

  issec-map-inv-equiv-bool-decidable-Prop' :
    (map-equiv-bool-decidable-Prop' ∘ map-inv-equiv-bool-decidable-Prop') ~ id
  issec-map-inv-equiv-bool-decidable-Prop' true = refl
  issec-map-inv-equiv-bool-decidable-Prop' false = refl

  isretr-map-inv-equiv-bool-decidable-Prop' :
    (map-inv-equiv-bool-decidable-Prop' ∘ map-equiv-bool-decidable-Prop') ~ id
  isretr-map-inv-equiv-bool-decidable-Prop' (inl x) =
    ap inl (eq-is-contr is-contr-total-true-Prop)
  isretr-map-inv-equiv-bool-decidable-Prop' (inr x) =
    ap inr (eq-is-contr is-contr-total-false-Prop)

  is-equiv-map-equiv-bool-decidable-Prop' :
    is-equiv map-equiv-bool-decidable-Prop'
  is-equiv-map-equiv-bool-decidable-Prop' =
    is-equiv-has-inverse
      map-inv-equiv-bool-decidable-Prop'
      issec-map-inv-equiv-bool-decidable-Prop'
      isretr-map-inv-equiv-bool-decidable-Prop'

  equiv-bool-decidable-Prop' :
    coprod (Σ (UU-Prop l) type-Prop) (Σ (UU-Prop l) (λ Q → ¬ (type-Prop Q))) ≃
    bool
  pr1 equiv-bool-decidable-Prop' = map-equiv-bool-decidable-Prop'
  pr2 equiv-bool-decidable-Prop' = is-equiv-map-equiv-bool-decidable-Prop'

  equiv-bool-decidable-Prop : decidable-Prop l ≃ bool
  equiv-bool-decidable-Prop = equiv-bool-decidable-Prop' ∘e split-decidable-Prop

  abstract
    compute-equiv-bool-decidable-Prop :
      (P : decidable-Prop l) →
      type-decidable-Prop P ≃ Id (map-equiv equiv-bool-decidable-Prop P) true
    compute-equiv-bool-decidable-Prop (pair P (pair H (inl p))) =
      equiv-is-contr
        ( is-proof-irrelevant-is-prop H p)
        ( is-proof-irrelevant-is-prop (is-set-bool true true) refl)
    compute-equiv-bool-decidable-Prop (pair P (pair H (inr np))) =
      equiv-is-empty np neq-false-true-bool
```
