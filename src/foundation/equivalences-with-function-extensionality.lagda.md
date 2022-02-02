# Equivalences with function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalences-with-function-extensionality where

open import foundation.contractible-maps using
  ( is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-Π; is-contr-is-equiv'; is-contr-prod;
    is-prop-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs using
  ( distributive-Π-Σ)
open import foundation.equivalences using
  ( is-equiv; sec; _≃_; map-equiv; map-inv-is-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (htpy-eq; funext)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv)
open import foundation.fundamental-theorem-of-identity-types using
  ( is-contr-total-htpy; fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl)
open import foundation.precomposition using (is-equiv-precomp-is-equiv)
open import foundation.retractions using (retr)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

We needed equivalences in order to introduce function extensionality. Using function extensionality, we can say more about equivalences.

## Properties

### Equivalences have a contractible type of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-sec-is-equiv : {f : A → B} → is-equiv f → is-contr (sec f)
  is-contr-sec-is-equiv {f} is-equiv-f =
    is-contr-equiv'
      ( (b : B) → fib f b)
      ( distributive-Π-Σ) 
      ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))
```

### Equivalences have a contractible type of retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-retr-is-equiv : {f : A → B} → is-equiv f → is-contr (retr f)
  is-contr-retr-is-equiv {f} is-equiv-f =
    is-contr-is-equiv'
      ( Σ (B → A) (λ h → Id (h ∘ f) id))
      ( tot (λ h → htpy-eq))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → funext (h ∘ f) id))
      ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)
```

### Being an equivalence is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f)

  abstract
    is-subtype-is-equiv : (f : A → B) → (H K : is-equiv f) → is-contr (Id H K)
    is-subtype-is-equiv f H =
      is-prop-is-contr (is-contr-is-equiv-is-equiv H) H

  is-equiv-Prop :
    (f : A → B) → Σ (UU (l1 ⊔ l2)) (λ X → (x y : X) → is-contr (Id x y))
  pr1 (is-equiv-Prop f) = is-equiv f
  pr2 (is-equiv-Prop f) = is-subtype-is-equiv f

{-
  abstract
    is-emb-map-equiv :
      is-emb (map-equiv {A = A} {B = B})
    is-emb-map-equiv = is-emb-pr1 is-subtype-is-equiv
-}
```

### Characterizing the identity type of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  htpy-eq-equiv : {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
  htpy-eq-equiv {e = e} {.e} refl =
    refl-htpy-equiv e

  abstract
    is-contr-total-htpy-equiv :
      (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
    is-contr-total-htpy-equiv (pair f is-equiv-f) =
      is-contr-total-Eq-subtype
        ( is-contr-total-htpy f)
        ( is-subtype-is-equiv)
        ( f)
        ( refl-htpy)
        ( is-equiv-f)

  is-equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → is-equiv (htpy-eq-equiv {e = e} {e'})
  is-equiv-htpy-eq-equiv e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-eq-equiv {e = e} {e'})

  equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → Id e e' ≃ (htpy-equiv e e')
  pr1 (equiv-htpy-eq-equiv e e') = htpy-eq-equiv
  pr2 (equiv-htpy-eq-equiv e e') = is-equiv-htpy-eq-equiv e e'

  eq-htpy-equiv : {e e' : A ≃ B} → ( htpy-equiv e e') → Id e e'
  eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-eq-equiv e e')
```
