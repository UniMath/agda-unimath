# The fundamental theorem of identity types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.fundamental-theorem-of-identity-types where

open import foundation.contractible-types using
  ( is-contr; is-equiv-is-contr; is-contr-total-path; is-contr-is-equiv';
    is-contr-equiv; is-contr-Σ; is-contr-retract-of)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-fiberwise-equiv; sec; is-equiv-sec-is-equiv)
open import foundation.functoriality-dependent-pair-types using
  ( tot; is-fiberwise-equiv-is-equiv-tot; is-equiv-tot-is-fiberwise-equiv;
    tot-comp; tot-htpy; tot-id)
open import foundation.homotopies using (inv-htpy; _∙h_)
open import foundation.identity-types using (Id; ind-Id)
open import foundation.retractions using (retr)
open import foundation.type-arithmetic-dependent-pair-types using
  ( interchange-Σ-Σ)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The fundamental theorem of identity type provides a way to characterize identity types. It uses the fact that a family of maps `f : (x : A) → Id a x → B x` is a family of equivalences if and only if it induces an equivalence `Σ A (Id a) → Σ A B` on total spaces. Note that the total space `Σ A (Id a)` is contractible. Therefore, any map `Σ A (Id a) → Σ A B` is an equivalence if and only if `Σ A B` is contractible.

## Theorem

For any family of maps `f : (x : A) → Id a x → B x`, the following are equivalent:
1. Each `f x` is an equivalence
2. The total space `Σ A B` is contractible.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

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
```

## Corollaries

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where
  
  abstract 
    fundamental-theorem-id-J :
      is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J is-contr-AB =
      fundamental-theorem-id a b is-contr-AB (ind-Id a (λ x p → B x) b)

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

### Retracts of the identity type are equivalent to the identity type

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

### The fundamental theorem of identity types, using sections

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
