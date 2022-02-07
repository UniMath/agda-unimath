# Equality on dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-dependent-function-types where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path; is-contr-Π)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs using
  ( Π-total-fam; distributive-Π-Σ)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.equivalences using (is-equiv; map-inv-is-equiv)
open import foundation.identity-types using (Id; tr; refl)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

```agda
is-contr-total-Eq-Π :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  ( is-contr-total-C : (x : A) → is-contr (Σ (B x) (C x))) →
  is-contr (Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
is-contr-total-Eq-Π {A = A} {B} C is-contr-total-C =
  is-contr-equiv'
    ( (x : A) → Σ (B x) (C x))
    ( distributive-Π-Σ)
    ( is-contr-Π is-contr-total-C)
```

```agda
{-
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (Eq-B : {x : A} → B x → B x → UU l3)
  (f : (x : A) → B x)
  where
  
extensionality-Π :
  ( (x : A) (y : B x) → Id (f x) y ≃ Eq-B y) →
  ( g : (x : A) → B x) → Id f g ≃ ((x : A) → Eq-B (g x))
  -}
```
