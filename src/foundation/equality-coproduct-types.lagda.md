---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.equality-coproduct-types where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path)
open import foundations.coproduct-types using
  ( coprod; inl; inr; ind-coprod;
    is-injective-inl; is-injective-inr; neq-inl-inr; neq-inr-inl)
open import foundation.decidable-equality using (has-decidable-equality)
open import foundation.decidable-types using (is-decidable-iff)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.empty-type using
  ( empty; is-empty; is-equiv-is-empty'; is-equiv-is-empty)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse; _∘e_; map-equiv; is-equiv-left-factor)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; ap; ap-comp; inv)
open import foundation.injective-maps using (is-injective)
open import foundation.levels using (Level; UU; _⊔_)
open import foundation.negation using (¬)
```

## Observational equality of coproduct types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coprod : coprod A B → coprod A B → UU (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : {x y : A} → Id x y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : {x y : B} → Id x y → Eq-coprod (inr x) (inr y)

  refl-Eq-coprod : (x : coprod A B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = Eq-eq-coprod-inl refl
  refl-Eq-coprod (inr x) = Eq-eq-coprod-inr refl

  Eq-eq-coprod : (x y : coprod A B) → Id x y → Eq-coprod x y
  Eq-eq-coprod x .x refl = refl-Eq-coprod x

  eq-Eq-coprod : (x y : coprod A B) → Eq-coprod x y → Id x y
  eq-Eq-coprod .(inl x) .(inl x) (Eq-eq-coprod-inl {x} {.x} refl) = refl
  eq-Eq-coprod .(inr x) .(inr x) (Eq-eq-coprod-inr {x} {.x} refl) = refl

  has-decidable-equality-coprod :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (coprod A B)
  has-decidable-equality-coprod d e (inl x) (inl y) =
    is-decidable-iff (ap inl) is-injective-inl (d x y)
  has-decidable-equality-coprod d e (inl x) (inr y) =
    inr neq-inl-inr
  has-decidable-equality-coprod d e (inr x) (inl y) =
    inr neq-inr-inl
  has-decidable-equality-coprod d e (inr x) (inr y) =
    is-decidable-iff (ap inr) is-injective-inr (e x y)

  has-decidable-equality-left-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality A
  has-decidable-equality-left-summand d x y =
    is-decidable-iff is-injective-inl (ap inl) (d (inl x) (inl y))

  has-decidable-equality-right-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality B
  has-decidable-equality-right-summand d x y =
    is-decidable-iff is-injective-inr (ap inr) (d (inr x) (inr y))
```

## The disjointness of coproducts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  -- The identity types of coproducts
  
  is-contr-total-Eq-coprod :
    (x : coprod A B) → is-contr (Σ (coprod A B) (Eq-coprod x))
  pr1 (pr1 (is-contr-total-Eq-coprod (inl x))) = inl x
  pr2 (pr1 (is-contr-total-Eq-coprod (inl x))) = Eq-eq-coprod-inl refl
  pr2
    ( is-contr-total-Eq-coprod (inl x))
    ( pair (inl .x) (Eq-eq-coprod-inl refl)) = refl
  pr1 (pr1 (is-contr-total-Eq-coprod (inr x))) = inr x
  pr2 (pr1 (is-contr-total-Eq-coprod (inr x))) = Eq-eq-coprod-inr refl
  pr2
    ( is-contr-total-Eq-coprod (inr x))
    ( pair .(inr x) (Eq-eq-coprod-inr refl)) = refl

  is-equiv-Eq-eq-coprod : (x y : coprod A B) → is-equiv (Eq-eq-coprod x y)
  is-equiv-Eq-eq-coprod x =
    fundamental-theorem-id x
      ( refl-Eq-coprod x)
      ( is-contr-total-Eq-coprod x)
      ( Eq-eq-coprod x)

  extensionality-coprod : (x y : coprod A B) → Id x y ≃ Eq-coprod x y
  pr1 (extensionality-coprod x y) = Eq-eq-coprod x y
  pr2 (extensionality-coprod x y) = is-equiv-Eq-eq-coprod x y

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  -- It should be possible to make these definitions abstract,
  -- but currently that breaks something in 23-pullbacks

  module _
    (x y : A)
    where
    
    map-compute-Eq-coprod-inl-inl : Eq-coprod {B = B} (inl x) (inl y) → Id x y
    map-compute-Eq-coprod-inl-inl (Eq-eq-coprod-inl p) = p

    issec-Eq-eq-coprod-inl :
      (map-compute-Eq-coprod-inl-inl ∘ Eq-eq-coprod-inl) ~ id
    issec-Eq-eq-coprod-inl p = refl

    isretr-Eq-eq-coprod-inl :
      (Eq-eq-coprod-inl ∘ map-compute-Eq-coprod-inl-inl) ~ id
    isretr-Eq-eq-coprod-inl (Eq-eq-coprod-inl p) = refl

    is-equiv-map-compute-Eq-coprod-inl-inl :
      is-equiv map-compute-Eq-coprod-inl-inl
    is-equiv-map-compute-Eq-coprod-inl-inl =
      is-equiv-has-inverse
        ( Eq-eq-coprod-inl)
        ( issec-Eq-eq-coprod-inl)
        ( isretr-Eq-eq-coprod-inl)

    compute-Eq-coprod-inl-inl : Eq-coprod (inl x) (inl y) ≃ Id x y
    pr1 compute-Eq-coprod-inl-inl = map-compute-Eq-coprod-inl-inl
    pr2 compute-Eq-coprod-inl-inl = is-equiv-map-compute-Eq-coprod-inl-inl

    compute-eq-coprod-inl-inl : Id {A = coprod A B} (inl x) (inl y) ≃ Id x y
    compute-eq-coprod-inl-inl =
      compute-Eq-coprod-inl-inl ∘e extensionality-coprod (inl x) (inl y)
      
    map-compute-eq-coprod-inl-inl : Id {A = coprod A B} (inl x) (inl y) → Id x y
    map-compute-eq-coprod-inl-inl = map-equiv compute-eq-coprod-inl-inl

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) → empty
    map-compute-Eq-coprod-inl-inr ()

    is-equiv-map-compute-Eq-coprod-inl-inr :
      is-equiv map-compute-Eq-coprod-inl-inr
    is-equiv-map-compute-Eq-coprod-inl-inr =
      is-equiv-is-empty' map-compute-Eq-coprod-inl-inr

    compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coprod-inl-inr = map-compute-Eq-coprod-inl-inr
    pr2 compute-Eq-coprod-inl-inr = is-equiv-map-compute-Eq-coprod-inl-inr

    compute-eq-coprod-inl-inr : Id {A = coprod A B} (inl x) (inr y) ≃ empty
    compute-eq-coprod-inl-inr =
      compute-Eq-coprod-inl-inr ∘e extensionality-coprod (inl x) (inr y)
      
    is-empty-eq-coprod-inl-inr : is-empty (Id {A = coprod A B} (inl x) (inr y))
    is-empty-eq-coprod-inl-inr = map-equiv compute-eq-coprod-inl-inr

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) → empty
    map-compute-Eq-coprod-inr-inl ()

    is-equiv-map-compute-Eq-coprod-inr-inl :
      is-equiv map-compute-Eq-coprod-inr-inl
    is-equiv-map-compute-Eq-coprod-inr-inl =
      is-equiv-is-empty' map-compute-Eq-coprod-inr-inl

    compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coprod-inr-inl = map-compute-Eq-coprod-inr-inl
    pr2 compute-Eq-coprod-inr-inl = is-equiv-map-compute-Eq-coprod-inr-inl

    compute-eq-coprod-inr-inl : Id {A = coprod A B} (inr x) (inl y) ≃ empty
    compute-eq-coprod-inr-inl =
      compute-Eq-coprod-inr-inl ∘e extensionality-coprod (inr x) (inl y)
      
    is-empty-eq-coprod-inr-inl : is-empty (Id {A = coprod A B} (inr x) (inl y))
    is-empty-eq-coprod-inr-inl = map-equiv compute-eq-coprod-inr-inl

  module _
    (x y : B)
    where
    
    map-compute-Eq-coprod-inr-inr : Eq-coprod {A = A} (inr x) (inr y) → Id x y
    map-compute-Eq-coprod-inr-inr (Eq-eq-coprod-inr p) = p

    issec-Eq-eq-coprod-inr :
      (map-compute-Eq-coprod-inr-inr ∘ Eq-eq-coprod-inr) ~ id
    issec-Eq-eq-coprod-inr p = refl

    isretr-Eq-eq-coprod-inr :
      (Eq-eq-coprod-inr ∘ map-compute-Eq-coprod-inr-inr) ~ id
    isretr-Eq-eq-coprod-inr (Eq-eq-coprod-inr p) = refl

    is-equiv-map-compute-Eq-coprod-inr-inr :
      is-equiv map-compute-Eq-coprod-inr-inr
    is-equiv-map-compute-Eq-coprod-inr-inr =
      is-equiv-has-inverse
        ( Eq-eq-coprod-inr)
        ( issec-Eq-eq-coprod-inr)
        ( isretr-Eq-eq-coprod-inr)

    compute-Eq-coprod-inr-inr : Eq-coprod (inr x) (inr y) ≃ Id x y
    pr1 compute-Eq-coprod-inr-inr = map-compute-Eq-coprod-inr-inr
    pr2 compute-Eq-coprod-inr-inr = is-equiv-map-compute-Eq-coprod-inr-inr

    compute-eq-coprod-inr-inr : Id {A = coprod A B} (inr x) (inr y) ≃ Id x y
    compute-eq-coprod-inr-inr =
      compute-Eq-coprod-inr-inr ∘e extensionality-coprod (inr x) (inr y)

    map-compute-eq-coprod-inr-inr : Id {A = coprod A B} (inr x) (inr y) → Id x y
    map-compute-eq-coprod-inr-inr = map-equiv compute-eq-coprod-inr-inr
```

## The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coprod-inl-inl x))
          ( is-contr-total-path x))
        ( λ y → ap inl)

  emb-inl : A ↪ coprod A B
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coprod-inr-inr x))
          ( is-contr-total-path x))
        ( λ y → ap inr)

  emb-inr : B ↪ coprod A B
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  is-emb-coprod :
    is-emb f → is-emb g → ((a : A) (b : B) → ¬ (Id (f a) (g b))) →
    is-emb (ind-coprod (λ x → C) f g)
  is-emb-coprod H K L (inl a) (inl a') =
    is-equiv-left-factor
      ( ap f)
      ( ap (ind-coprod (λ x → C) f g))
      ( ap inl)
      ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
      ( H a a')
      ( is-emb-inl A B a a')
  is-emb-coprod H K L (inl a) (inr b') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
  is-emb-coprod H K L (inr b) (inl a') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
  is-emb-coprod H K L (inr b) (inr b') =
    is-equiv-left-factor
      ( ap g)
      ( ap (ind-coprod (λ x → C) f g))
      ( ap inr)
      ( λ p → ap-comp (ind-coprod (λ x → C) f g) inr p)
      ( K b b')
      ( is-emb-inr A B b b')
```
