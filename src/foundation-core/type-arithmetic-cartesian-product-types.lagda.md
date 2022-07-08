---
title: Type arithmetic for cartesian product types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.type-arithmetic-cartesian-product-types where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.contractible-types using (is-contr; center)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (refl)
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

We prove laws for the manipulation of cartesian products with respect to itself and dependent pair types. The arithmetical laws involving coproduct types are proven in `type-arithmetic-coproduct-types`, and the laws involving the unit type and the empty type are proven in `type-arithmetic-unit-type` and `type-arithmetic-empty-type` respectively.

## Laws

### Commutativity of cartesian products

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-prod : A × B → B × A
  pr1 (map-commutative-prod (pair a b)) = b
  pr2 (map-commutative-prod (pair a b)) = a
  
  map-inv-commutative-prod : B × A → A × B
  pr1 (map-inv-commutative-prod (pair b a)) = a
  pr2 (map-inv-commutative-prod (pair b a)) = b

  issec-map-inv-commutative-prod :
    (map-commutative-prod ∘ map-inv-commutative-prod) ~ id
  issec-map-inv-commutative-prod (pair b a) = refl

  isretr-map-inv-commutative-prod :
    (map-inv-commutative-prod ∘ map-commutative-prod) ~ id
  isretr-map-inv-commutative-prod (pair a b) = refl

  is-equiv-map-commutative-prod : is-equiv map-commutative-prod
  is-equiv-map-commutative-prod =
    is-equiv-has-inverse
      map-inv-commutative-prod
      issec-map-inv-commutative-prod
      isretr-map-inv-commutative-prod

  commutative-prod : (A × B) ≃ (B × A)
  pr1 commutative-prod = map-commutative-prod
  pr2 commutative-prod = is-equiv-map-commutative-prod
```

### Associativity of cartesian products

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where
  
  map-assoc-prod : (A × B) × C → A × (B × C)
  map-assoc-prod = map-assoc-Σ A (λ x → B) (λ w → C)

  map-inv-assoc-prod : A × (B × C) → (A × B) × C
  map-inv-assoc-prod = map-inv-assoc-Σ A (λ x → B) (λ w → C)

  issec-map-inv-assoc-prod : (map-assoc-prod ∘ map-inv-assoc-prod) ~ id
  issec-map-inv-assoc-prod = issec-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  isretr-map-inv-assoc-prod : (map-inv-assoc-prod ∘ map-assoc-prod) ~ id
  isretr-map-inv-assoc-prod = isretr-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  is-equiv-map-assoc-prod : is-equiv map-assoc-prod
  is-equiv-map-assoc-prod = is-equiv-map-assoc-Σ A (λ x → B) (λ w → C)

  assoc-prod : ((A × B) × C) ≃ (A × (B × C))
  assoc-prod = assoc-Σ A (λ x → B) (λ w → C)
```

### The unit laws of cartesian product types with respect to contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  right-unit-law-prod-is-contr : is-contr B → (A × B) ≃ A
  right-unit-law-prod-is-contr H = right-unit-law-Σ-is-contr (λ a → H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (C : is-contr A)
  where
  
  left-unit-law-prod-is-contr : (A × B) ≃ B
  left-unit-law-prod-is-contr =
    left-unit-law-Σ-is-contr C (center C)
```
