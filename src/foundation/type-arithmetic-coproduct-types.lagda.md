---
title: Type arithmetic for coproduct types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.type-arithmetic-coproduct-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inl-inr; neq-inr-inl)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; issec-map-inv-is-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (refl)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We prove laws for the manipulation of coproduct types with respect to itself, cartesian products, and dependent pair types. The arithmetical laws involving the unit type and the empty type are proven in `type-arithmetic-unit-type` and `type-arithmetic-empty-type` respectively.

## Laws

### Commutativity of coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  map-commutative-coprod : coprod A B → coprod B A
  map-commutative-coprod (inl a) = inr a
  map-commutative-coprod (inr b) = inl b
  
  map-inv-commutative-coprod : coprod B A → coprod A B
  map-inv-commutative-coprod (inl b) = inr b
  map-inv-commutative-coprod (inr a) = inl a
  
  issec-map-inv-commutative-coprod :
    ( map-commutative-coprod ∘ map-inv-commutative-coprod) ~ id
  issec-map-inv-commutative-coprod (inl b) = refl
  issec-map-inv-commutative-coprod (inr a) = refl
  
  isretr-map-inv-commutative-coprod :
    ( map-inv-commutative-coprod ∘ map-commutative-coprod) ~ id
  isretr-map-inv-commutative-coprod (inl a) = refl
  isretr-map-inv-commutative-coprod (inr b) = refl

  is-equiv-map-commutative-coprod : is-equiv map-commutative-coprod
  is-equiv-map-commutative-coprod =
    is-equiv-has-inverse
      map-inv-commutative-coprod
      issec-map-inv-commutative-coprod
      isretr-map-inv-commutative-coprod

  commutative-coprod : coprod A B ≃ coprod B A
  pr1 commutative-coprod = map-commutative-coprod
  pr2 commutative-coprod = is-equiv-map-commutative-coprod
```

### Associativity of coproducts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  map-assoc-coprod : coprod (coprod A B) C → coprod A (coprod B C)
  map-assoc-coprod (inl (inl x)) = inl x
  map-assoc-coprod (inl (inr x)) = inr (inl x)
  map-assoc-coprod (inr x) = inr (inr x)

  map-inv-assoc-coprod : coprod A (coprod B C) → coprod (coprod A B) C
  map-inv-assoc-coprod (inl x) = inl (inl x)
  map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
  map-inv-assoc-coprod (inr (inr x)) = inr x

  issec-map-inv-assoc-coprod : (map-assoc-coprod ∘ map-inv-assoc-coprod) ~ id
  issec-map-inv-assoc-coprod (inl x) = refl
  issec-map-inv-assoc-coprod (inr (inl x)) = refl
  issec-map-inv-assoc-coprod (inr (inr x)) = refl

  isretr-map-inv-assoc-coprod : (map-inv-assoc-coprod ∘ map-assoc-coprod) ~ id
  isretr-map-inv-assoc-coprod (inl (inl x)) = refl
  isretr-map-inv-assoc-coprod (inl (inr x)) = refl
  isretr-map-inv-assoc-coprod (inr x) = refl

  is-equiv-map-assoc-coprod : is-equiv map-assoc-coprod
  is-equiv-map-assoc-coprod =
    is-equiv-has-inverse
      map-inv-assoc-coprod
      issec-map-inv-assoc-coprod
      isretr-map-inv-assoc-coprod

  is-equiv-map-inv-assoc-coprod : is-equiv map-inv-assoc-coprod
  is-equiv-map-inv-assoc-coprod =
    is-equiv-has-inverse
      map-assoc-coprod
      isretr-map-inv-assoc-coprod
      issec-map-inv-assoc-coprod

  assoc-coprod : coprod (coprod A B) C ≃ coprod A (coprod B C)
  pr1 assoc-coprod = map-assoc-coprod
  pr2 assoc-coprod = is-equiv-map-assoc-coprod
  
  inv-assoc-coprod : coprod A (coprod B C) ≃ coprod (coprod A B) C
  pr1 inv-assoc-coprod = map-inv-assoc-coprod
  pr2 inv-assoc-coprod = is-equiv-map-inv-assoc-coprod
```

### Right distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3)
  where
  
  map-right-distributive-Σ-coprod :
    Σ (coprod A B) C → coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coprod (pair (inl x) z) = inl (pair x z)
  map-right-distributive-Σ-coprod (pair (inr y) z) = inr (pair y z)

  map-inv-right-distributive-Σ-coprod :
    coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
  pr1 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = inl x
  pr2 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = z
  pr1 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = inr y
  pr2 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = z

  issec-map-inv-right-distributive-Σ-coprod :
    ( map-right-distributive-Σ-coprod ∘ map-inv-right-distributive-Σ-coprod) ~
    ( id)
  issec-map-inv-right-distributive-Σ-coprod (inl (pair x z)) = refl
  issec-map-inv-right-distributive-Σ-coprod (inr (pair y z)) = refl

  isretr-map-inv-right-distributive-Σ-coprod :
    ( map-inv-right-distributive-Σ-coprod ∘ map-right-distributive-Σ-coprod) ~
    ( id)
  isretr-map-inv-right-distributive-Σ-coprod (pair (inl x) z) = refl
  isretr-map-inv-right-distributive-Σ-coprod (pair (inr y) z) = refl

  abstract
    is-equiv-map-right-distributive-Σ-coprod :
      is-equiv map-right-distributive-Σ-coprod
    is-equiv-map-right-distributive-Σ-coprod =
      is-equiv-has-inverse
        map-inv-right-distributive-Σ-coprod
        issec-map-inv-right-distributive-Σ-coprod
        isretr-map-inv-right-distributive-Σ-coprod

  right-distributive-Σ-coprod :
    Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  pr1 right-distributive-Σ-coprod = map-right-distributive-Σ-coprod
  pr2 right-distributive-Σ-coprod = is-equiv-map-right-distributive-Σ-coprod
```

### Left distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3)
  where

  map-left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
  map-left-distributive-Σ-coprod (pair x (inl y)) = inl (pair x y)
  map-left-distributive-Σ-coprod (pair x (inr z)) = inr (pair x z)

  map-inv-left-distributive-Σ-coprod :
    coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
  pr1 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = inl y
  pr1 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = inr z

  issec-map-inv-left-distributive-Σ-coprod :
    ( map-left-distributive-Σ-coprod ∘ map-inv-left-distributive-Σ-coprod) ~ id
  issec-map-inv-left-distributive-Σ-coprod (inl (pair x y)) = refl
  issec-map-inv-left-distributive-Σ-coprod (inr (pair x z)) = refl

  isretr-map-inv-left-distributive-Σ-coprod :
    ( map-inv-left-distributive-Σ-coprod ∘ map-left-distributive-Σ-coprod) ~ id
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inl y)) = refl
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inr z)) = refl

  is-equiv-map-left-distributive-Σ-coprod :
    is-equiv map-left-distributive-Σ-coprod
  is-equiv-map-left-distributive-Σ-coprod =
    is-equiv-has-inverse
      map-inv-left-distributive-Σ-coprod
      issec-map-inv-left-distributive-Σ-coprod
      isretr-map-inv-left-distributive-Σ-coprod

  left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
  pr1 left-distributive-Σ-coprod = map-left-distributive-Σ-coprod
  pr2 left-distributive-Σ-coprod = is-equiv-map-left-distributive-Σ-coprod
```

### Right distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-right-distributive-prod-coprod : (coprod A B) × C → coprod (A × C) (B × C)
  map-right-distributive-prod-coprod =
    map-right-distributive-Σ-coprod A B (λ x → C)

  map-inv-right-distributive-prod-coprod :
    coprod (A × C) (B × C) → (coprod A B) × C
  map-inv-right-distributive-prod-coprod =
    map-inv-right-distributive-Σ-coprod A B (λ x → C)

  issec-map-inv-right-distributive-prod-coprod :
    ( map-right-distributive-prod-coprod ∘
      map-inv-right-distributive-prod-coprod) ~ id
  issec-map-inv-right-distributive-prod-coprod =
    issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  isretr-map-inv-right-distributive-prod-coprod :
    ( map-inv-right-distributive-prod-coprod ∘
      map-right-distributive-prod-coprod) ~ id
  isretr-map-inv-right-distributive-prod-coprod =
    isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  abstract
    is-equiv-map-right-distributive-prod-coprod :
      is-equiv map-right-distributive-prod-coprod
    is-equiv-map-right-distributive-prod-coprod =
      is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)
  
  right-distributive-prod-coprod : ((coprod A B) × C) ≃ coprod (A × C) (B × C)
  right-distributive-prod-coprod = right-distributive-Σ-coprod A B (λ x → C)
```

### Left distributivity of products over coproducts

```
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-left-distributive-prod-coprod : A × (coprod B C) → coprod (A × B) (A × C)
  map-left-distributive-prod-coprod =
    map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  map-inv-left-distributive-prod-coprod :
    coprod (A × B) (A × C) → A × (coprod B C)
  map-inv-left-distributive-prod-coprod =
    map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  issec-map-inv-left-distributive-prod-coprod :
    ( map-left-distributive-prod-coprod ∘
      map-inv-left-distributive-prod-coprod) ~ id
  issec-map-inv-left-distributive-prod-coprod =
    issec-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  isretr-map-inv-left-distributive-prod-coprod :
    ( map-inv-left-distributive-prod-coprod ∘
      map-left-distributive-prod-coprod) ~ id
  isretr-map-inv-left-distributive-prod-coprod =
    isretr-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-equiv-map-left-distributive-prod-coprod :
    is-equiv map-left-distributive-prod-coprod
  is-equiv-map-left-distributive-prod-coprod =
    is-equiv-map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  left-distributive-prod-coprod : (A × (coprod B C)) ≃ coprod (A × B) (A × C)
  left-distributive-prod-coprod =
    left-distributive-Σ-coprod A (λ x → B) (λ x → C)
```
