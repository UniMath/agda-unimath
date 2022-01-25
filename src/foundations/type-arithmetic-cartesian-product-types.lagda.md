---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.type-arithmetic-cartesian-product-types where

open import foundations.contractible-types using (is-contr; center)
open import foundations.cartesian-product-types using (_×_)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; is-empty; ex-falso)
open import foundations.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_)
open import foundations.functions using (_∘_; id)
open import foundations.homotopies using (_~_)
open import foundations.identity-types using (refl)
open import foundations.levels using (Level; UU)
open import foundations.type-arithmetic-dependent-pair-types
open import foundations.unit-type using (unit; star)
```

# Type arithmetic for cartesian product types

In this file we prove arithmetical laws for cartesian product types, including laws that also involve dependent pair types. The arithmetical laws involving coproduct types are proven in `type-arithmetic-coproduct-types`.

## Commutativity of cartesian products

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

## Associativity of cartesian products

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

## Left zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr1-prod-empty : empty → empty × X
  inv-pr1-prod-empty ()

  issec-inv-pr1-prod-empty : (pr1 ∘ inv-pr1-prod-empty) ~ id
  issec-inv-pr1-prod-empty ()

  isretr-inv-pr1-prod-empty : (inv-pr1-prod-empty ∘ pr1) ~ id
  isretr-inv-pr1-prod-empty (pair () x)

  is-equiv-pr1-prod-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-prod-empty =
    is-equiv-has-inverse
      inv-pr1-prod-empty
      issec-inv-pr1-prod-empty
      isretr-inv-pr1-prod-empty

  left-zero-law-prod : (empty × X) ≃ empty
  pr1 left-zero-law-prod = pr1
  pr2 left-zero-law-prod = is-equiv-pr1-prod-empty
```

## Right zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr2-prod-empty : empty → (X × empty)
  inv-pr2-prod-empty ()

  issec-inv-pr2-prod-empty : (pr2 ∘ inv-pr2-prod-empty) ~ id
  issec-inv-pr2-prod-empty ()

  isretr-inv-pr2-prod-empty : (inv-pr2-prod-empty ∘ pr2) ~ id
  isretr-inv-pr2-prod-empty (pair x ())

  is-equiv-pr2-prod-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-prod-empty =
    is-equiv-has-inverse
      inv-pr2-prod-empty
      issec-inv-pr2-prod-empty
      isretr-inv-pr2-prod-empty

  right-zero-law-prod : (X × empty) ≃ empty
  pr1 right-zero-law-prod = pr2
  pr2 right-zero-law-prod = is-equiv-pr2-prod-empty
```

## Right absorption law for cartesian product types

```agda
module _
  {l : Level} {A : UU l}
  where
  
  map-right-absorption-prod : A × empty → empty
  map-right-absorption-prod = map-right-absorption-Σ A

  is-equiv-map-right-absorption-prod : is-equiv map-right-absorption-prod
  is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ A

  right-absorption-prod : (A × empty) ≃ empty
  right-absorption-prod = right-absorption-Σ A

is-empty-right-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → A → is-empty B
is-empty-right-factor-is-empty-prod f a b = f (pair a b)
```

## Left absorption law for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-absorption-prod : empty × A → empty
  map-left-absorption-prod = map-left-absorption-Σ (λ x → A)
  
  is-equiv-map-left-absorption-prod : is-equiv map-left-absorption-prod
  is-equiv-map-left-absorption-prod =
    is-equiv-map-left-absorption-Σ (λ x → A)
    
  left-absorption-prod : (empty × A) ≃ empty
  left-absorption-prod = left-absorption-Σ (λ x → A)

is-empty-left-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → B → is-empty A
is-empty-left-factor-is-empty-prod f b a = f (pair a b)
```

## Left unit law for cartesian products

```agda
module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-prod : unit × A → A
  map-left-unit-law-prod = pr2

  map-inv-left-unit-law-prod : A → unit × A
  map-inv-left-unit-law-prod = map-inv-left-unit-law-Σ (λ x → A)

  issec-map-inv-left-unit-law-prod :
    ( map-left-unit-law-prod ∘ map-inv-left-unit-law-prod) ~ id
  issec-map-inv-left-unit-law-prod =
    issec-map-inv-left-unit-law-Σ (λ x → A)

  isretr-map-inv-left-unit-law-prod :
    ( map-inv-left-unit-law-prod ∘ map-left-unit-law-prod) ~ id
  isretr-map-inv-left-unit-law-prod (pair star a) = refl

  is-equiv-map-left-unit-law-prod : is-equiv map-left-unit-law-prod
  is-equiv-map-left-unit-law-prod =
    is-equiv-has-inverse
      map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod

  left-unit-law-prod : (unit × A) ≃ A
  pr1 left-unit-law-prod = map-left-unit-law-prod
  pr2 left-unit-law-prod = is-equiv-map-left-unit-law-prod

  is-equiv-map-inv-left-unit-law-prod : is-equiv map-inv-left-unit-law-prod
  is-equiv-map-inv-left-unit-law-prod =
    is-equiv-has-inverse
      map-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod

  inv-left-unit-law-prod : A ≃ (unit × A)
  pr1 inv-left-unit-law-prod = map-inv-left-unit-law-prod
  pr2 inv-left-unit-law-prod = is-equiv-map-inv-left-unit-law-prod

  map-right-unit-law-prod : A × unit → A
  map-right-unit-law-prod = pr1

  map-inv-right-unit-law-prod : A → A × unit
  pr1 (map-inv-right-unit-law-prod a) = a
  pr2 (map-inv-right-unit-law-prod a) = star

  issec-map-inv-right-unit-law-prod :
    (map-right-unit-law-prod ∘ map-inv-right-unit-law-prod) ~ id
  issec-map-inv-right-unit-law-prod a = refl

  isretr-map-inv-right-unit-law-prod :
    (map-inv-right-unit-law-prod ∘ map-right-unit-law-prod) ~ id
  isretr-map-inv-right-unit-law-prod (pair a star) = refl

  is-equiv-map-right-unit-law-prod : is-equiv map-right-unit-law-prod
  is-equiv-map-right-unit-law-prod =
    is-equiv-has-inverse
      map-inv-right-unit-law-prod
      issec-map-inv-right-unit-law-prod
      isretr-map-inv-right-unit-law-prod

  right-unit-law-prod : (A × unit) ≃ A
  pr1 right-unit-law-prod = map-right-unit-law-prod
  pr2 right-unit-law-prod = is-equiv-map-right-unit-law-prod

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

## Swapping a cartesian product inside a Σ-type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (pair a (pair b c))) = b
  pr1 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = a
  pr2 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = c
  
  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (pair b (pair a c))) = a
  pr1 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = b
  pr2 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = c
  
  isretr-map-inv-left-swap-Σ : (map-inv-left-swap-Σ ∘ map-left-swap-Σ) ~ id
  isretr-map-inv-left-swap-Σ (pair a (pair b c)) = refl

  issec-map-inv-left-swap-Σ : (map-left-swap-Σ ∘ map-inv-left-swap-Σ) ~ id
  issec-map-inv-left-swap-Σ (pair b (pair a c)) = refl
  
  abstract
    is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
    is-equiv-map-left-swap-Σ =
      is-equiv-has-inverse
        map-inv-left-swap-Σ
        issec-map-inv-left-swap-Σ
        isretr-map-inv-left-swap-Σ
  
  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = map-left-swap-Σ
  pr2 equiv-left-swap-Σ = is-equiv-map-left-swap-Σ
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  pr1 (pr1 (map-right-swap-Σ (pair (pair a b) c))) = a
  pr2 (pr1 (map-right-swap-Σ (pair (pair a b) c))) = c
  pr2 (map-right-swap-Σ (pair (pair a b) c)) = b

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  pr1 (pr1 (map-inv-right-swap-Σ (pair (pair a c) b))) = a
  pr2 (pr1 (map-inv-right-swap-Σ (pair (pair a c) b))) = b
  pr2 (map-inv-right-swap-Σ (pair (pair a c) b)) = c

  issec-map-inv-right-swap-Σ : (map-right-swap-Σ ∘ map-inv-right-swap-Σ) ~ id
  issec-map-inv-right-swap-Σ (pair (pair x y) z) = refl

  isretr-map-inv-right-swap-Σ : (map-inv-right-swap-Σ ∘ map-right-swap-Σ) ~ id
  isretr-map-inv-right-swap-Σ (pair (pair x z) y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-has-inverse
      map-inv-right-swap-Σ
      issec-map-inv-right-swap-Σ
      isretr-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  pr1 equiv-right-swap-Σ = map-right-swap-Σ
  pr2 equiv-right-swap-Σ = is-equiv-map-right-swap-Σ
```
