---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.fundamental-theorem-of-identity-types where

open import foundation.contractible-types using
  ( is-contr; is-equiv-is-contr; is-contr-total-path; is-contr-is-equiv';
    is-contr-equiv; is-contr-Σ; is-contr-retract-of)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-fiberwise-equiv; retr; sec; is-equiv-sec-is-equiv)
open import foundation.functoriality-dependent-pair-types using
  ( tot; is-fiberwise-equiv-is-equiv-tot; is-equiv-tot-is-fiberwise-equiv;
    tot-comp; tot-htpy; tot-id)
open import foundation.homotopies using (inv-htpy; _∙h_)
open import foundation.identity-types using (Id; ind-Id)
open import foundation.universe-levels using (Level; UU)
open import foundation.type-arithmetic-dependent-pair-types using
  ( interchange-Σ-Σ)
```

# The fundamental theorem of identity types

The fundamental theorem of identity types asserts that for any family of maps `f : (x : A) → Id a x → B x`, the following are equivalent:
1. Each `f x` is an equivalence
2. The total space `Σ A B` is contractible.

We will use this result often to characterize the identity type of a given type.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  -- The general form of the fundamental theorem of identity types
  
  abstract
    fundamental-theorem-id :
      is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id is-contr-AB f =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f → is-contr (Σ A B)
    fundamental-theorem-id' f is-fiberwise-equiv-f =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot f)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
        ( is-contr-total-path a)

  -- The canonical form of the fundamental theorem of identity types
  
  abstract 
    fundamental-theorem-id-J :
      is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J is-contr-AB =
      fundamental-theorem-id is-contr-AB (ind-Id a (λ x p → B x) b)

  -- The converse of the fundamental theorem of identity types
  
  abstract
    fundamental-theorem-id-J' :
      (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
    fundamental-theorem-id-J' H =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot (ind-Id a (λ x p → B x) b))
        ( is-equiv-tot-is-fiberwise-equiv H)
        ( is-contr-total-path a)
```

# Retracts of the identity type are equivalent to the identity type

```agda
module _
  {i j : Level} {A : UU i} {B : A → UU j} (a : A)
  where

  abstract
    fundamental-theorem-id-retr :
      (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retr i R =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot i)
          ( is-contr-retract-of (Σ _ (λ y → Id a y))
            ( pair (tot i)
              ( pair (tot λ x → pr1 (R x))
                ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
                  ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
            ( is-contr-total-path a))
          ( is-contr-total-path a))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-sec :
      (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
      is-fiberwise-equiv f
    fundamental-theorem-id-sec f sec-f x =
      is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)
      where
        i : (x : A) → B x → Id a x
        i = λ x → pr1 (sec-f x)
        retr-i : (x : A) → retr (i x)
        pr1 (retr-i x) = f x
        pr2 (retr-i x) = pr2 (sec-f x)
        is-fiberwise-equiv-i : is-fiberwise-equiv i
        is-fiberwise-equiv-i = fundamental-theorem-id-retr a i retr-i
```

## Structure identity principle

```agda
module _
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where
    
  abstract
    is-contr-total-Eq-structure :
      (is-contr-AC : is-contr (Σ A C)) (t : Σ A C) →
      is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
      is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
    is-contr-total-Eq-structure is-contr-AC t is-contr-BD =
      is-contr-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
        ( interchange-Σ-Σ D)
        ( is-contr-Σ is-contr-AC t is-contr-BD)
```
