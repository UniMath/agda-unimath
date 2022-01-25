---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.fundamental-theorem-of-identity-types where

open import foundations.contractible-types using
  ( is-contr; is-equiv-is-contr; is-contr-total-path; is-contr-is-equiv';
    is-contr-equiv; is-contr-Σ)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.equivalences using (is-equiv; is-fiberwise-equiv)
open import foundations.functoriality-dependent-pair-types using
  ( tot; is-fiberwise-equiv-is-equiv-tot; is-equiv-tot-is-fiberwise-equiv)
open import foundations.identity-types using (Id; ind-Id)
open import foundations.levels using (Level; UU)
open import foundations.type-arithmetic-dependent-pair-types using
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
