---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.type-arithmetic-coproduct-types where

open import foundations.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; is-empty; ex-falso)
open import foundations.equivalences using (is-equiv; is-equiv-has-inverse; _≃_)
open import foundations.functions using (_∘_; id)
open import foundations.homotopies using (_~_; refl-htpy)
open import foundations.identity-types using (refl)
open import foundations.levels using (Level; UU)
```

# Type arithmetic for coproduct types

In this file we prove arithmetical laws for cartesian product types, including laws that also involve dependent pair types and cartesian product types

## Left unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A)
  where

  map-left-unit-law-coprod-is-empty : coprod A B → B
  map-left-unit-law-coprod-is-empty (inl a) = ex-falso (H a)
  map-left-unit-law-coprod-is-empty (inr b) = b

  map-inv-left-unit-law-coprod-is-empty : B → coprod A B
  map-inv-left-unit-law-coprod-is-empty = inr

  issec-map-inv-left-unit-law-coprod-is-empty :
    ( map-left-unit-law-coprod-is-empty ∘
      map-inv-left-unit-law-coprod-is-empty) ~ id
  issec-map-inv-left-unit-law-coprod-is-empty = refl-htpy

  isretr-map-inv-left-unit-law-coprod-is-empty :
    ( map-inv-left-unit-law-coprod-is-empty ∘
      map-left-unit-law-coprod-is-empty) ~ id
  isretr-map-inv-left-unit-law-coprod-is-empty (inl a) = ex-falso (H a)
  isretr-map-inv-left-unit-law-coprod-is-empty (inr b) = refl

  is-equiv-map-left-unit-law-coprod-is-empty :
    is-equiv map-left-unit-law-coprod-is-empty
  is-equiv-map-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-left-unit-law-coprod-is-empty
      issec-map-inv-left-unit-law-coprod-is-empty
      isretr-map-inv-left-unit-law-coprod-is-empty

  left-unit-law-coprod-is-empty : coprod A B ≃ B
  pr1 left-unit-law-coprod-is-empty = map-left-unit-law-coprod-is-empty
  pr2 left-unit-law-coprod-is-empty = is-equiv-map-left-unit-law-coprod-is-empty

  inv-left-unit-law-coprod-is-empty : B ≃ coprod A B
  pr1 inv-left-unit-law-coprod-is-empty = map-inv-left-unit-law-coprod-is-empty
  pr2 inv-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-left-unit-law-coprod-is-empty)
      ( isretr-map-inv-left-unit-law-coprod-is-empty)
      ( issec-map-inv-left-unit-law-coprod-is-empty)

module _
  {l : Level} (B : UU l)
  where

  map-left-unit-law-coprod : coprod empty B → B
  map-left-unit-law-coprod = map-left-unit-law-coprod-is-empty empty B id

  map-inv-left-unit-law-coprod : B → coprod empty B
  map-inv-left-unit-law-coprod = inr

  issec-map-inv-left-unit-law-coprod :
    ( map-left-unit-law-coprod ∘ map-inv-left-unit-law-coprod) ~ id
  issec-map-inv-left-unit-law-coprod =
    issec-map-inv-left-unit-law-coprod-is-empty empty B id

  isretr-map-inv-left-unit-law-coprod :
    ( map-inv-left-unit-law-coprod ∘ map-left-unit-law-coprod) ~ id
  isretr-map-inv-left-unit-law-coprod =
    isretr-map-inv-left-unit-law-coprod-is-empty empty B id

  is-equiv-map-left-unit-law-coprod : is-equiv map-left-unit-law-coprod
  is-equiv-map-left-unit-law-coprod =
    is-equiv-map-left-unit-law-coprod-is-empty empty B id
  
  left-unit-law-coprod : coprod empty B ≃ B
  left-unit-law-coprod = left-unit-law-coprod-is-empty empty B id

  inv-left-unit-law-coprod : B ≃ (coprod empty B)
  inv-left-unit-law-coprod = inv-left-unit-law-coprod-is-empty empty B id
```

## Right unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B)
  where

  map-right-unit-law-coprod-is-empty : coprod A B → A
  map-right-unit-law-coprod-is-empty (inl a) = a
  map-right-unit-law-coprod-is-empty (inr b) = ex-falso (H b)
  
  map-inv-right-unit-law-coprod-is-empty : A → coprod A B
  map-inv-right-unit-law-coprod-is-empty = inl

  issec-map-inv-right-unit-law-coprod-is-empty :
    ( map-right-unit-law-coprod-is-empty ∘
      map-inv-right-unit-law-coprod-is-empty) ~ id
  issec-map-inv-right-unit-law-coprod-is-empty a = refl

  isretr-map-inv-right-unit-law-coprod-is-empty :
    ( map-inv-right-unit-law-coprod-is-empty ∘
      map-right-unit-law-coprod-is-empty) ~ id
  isretr-map-inv-right-unit-law-coprod-is-empty (inl a) = refl
  isretr-map-inv-right-unit-law-coprod-is-empty (inr b) = ex-falso (H b)

  is-equiv-map-right-unit-law-coprod-is-empty :
    is-equiv map-right-unit-law-coprod-is-empty
  is-equiv-map-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-right-unit-law-coprod-is-empty
      issec-map-inv-right-unit-law-coprod-is-empty
      isretr-map-inv-right-unit-law-coprod-is-empty

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

  right-unit-law-coprod-is-empty : coprod A B ≃ A
  pr1 right-unit-law-coprod-is-empty = map-right-unit-law-coprod-is-empty
  pr2 right-unit-law-coprod-is-empty =
    is-equiv-map-right-unit-law-coprod-is-empty

  inv-right-unit-law-coprod-is-empty : A ≃ (coprod A B)
  pr1 inv-right-unit-law-coprod-is-empty = inl
  pr2 inv-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

module _
  {l : Level} (A : UU l)
  where

  map-right-unit-law-coprod : coprod A empty → A
  map-right-unit-law-coprod = map-right-unit-law-coprod-is-empty A empty id

  map-inv-right-unit-law-coprod : A → coprod A empty
  map-inv-right-unit-law-coprod = inl

  issec-map-inv-right-unit-law-coprod :
    ( map-right-unit-law-coprod ∘ map-inv-right-unit-law-coprod) ~ id
  issec-map-inv-right-unit-law-coprod =
    issec-map-inv-right-unit-law-coprod-is-empty A empty id

  isretr-map-inv-right-unit-law-coprod :
    ( map-inv-right-unit-law-coprod ∘ map-right-unit-law-coprod) ~ id
  isretr-map-inv-right-unit-law-coprod =
    isretr-map-inv-right-unit-law-coprod-is-empty A empty id

  is-equiv-map-right-unit-law-coprod : is-equiv map-right-unit-law-coprod
  is-equiv-map-right-unit-law-coprod =
    is-equiv-map-right-unit-law-coprod-is-empty A empty id

  right-unit-law-coprod : coprod A empty ≃ A
  right-unit-law-coprod = right-unit-law-coprod-is-empty A empty id

  inv-right-unit-law-coprod : A ≃ coprod A empty
  inv-right-unit-law-coprod =
    inv-right-unit-law-coprod-is-empty A empty id
```

## Commutativity of coproducts

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
```

## Associativity of coproducts

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

## Right distributivity of Σ over coproducts

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

## Left distributivity of Σ over coproducts

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

## Right distributivity of products over coproducts

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

## Left distributivity of products over coproducts

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
