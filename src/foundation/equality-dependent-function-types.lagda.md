# Equality on dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-dependent-function-types where

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation-core.equivalences using
  ( is-equiv; map-inv-is-equiv; _≃_; map-equiv; is-equiv-map-equiv)
open import foundation-core.identity-types using (Id; tr; refl)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path; is-contr-Π)
open import
  foundation.type-theoretic-principle-of-choice using
  ( Π-total-fam; distributive-Π-Σ)
```

## Idea

Given a family of types `B` over `A`, if we can characterize the identity types of each `B x`, then we can characterize the identity types of `(x : A) → B x`.

### Contractibility

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

### Extensionality

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x)
  (Eq-B : (x : A) → B x → UU l3)
  where

  map-extensionality-Π :
    ( (x : A) (y : B x) → Id (f x) y ≃ Eq-B x y) →
    ( g : (x : A) → B x) → Id f g → ((x : A) → Eq-B x (g x))
  map-extensionality-Π e .f refl x = map-equiv (e x (f x)) refl

  abstract
    is-equiv-map-extensionality-Π :
      (e : (x : A) (y : B x) → Id (f x) y ≃ Eq-B x y) →
      (g : (x : A) → B x) → is-equiv (map-extensionality-Π e g)
    is-equiv-map-extensionality-Π e =
      fundamental-theorem-id f
        ( map-extensionality-Π e f refl)
        ( is-contr-total-Eq-Π Eq-B
          ( λ x →
            fundamental-theorem-id'
              ( f x)
              ( map-equiv (e x (f x)) refl)
              ( λ y → map-equiv (e x y))
              ( λ y → is-equiv-map-equiv (e x y))))
        ( map-extensionality-Π e)
  
  extensionality-Π :
    ( (x : A) (y : B x) → Id (f x) y ≃ Eq-B x y) →
    ( g : (x : A) → B x) → Id f g ≃ ((x : A) → Eq-B x (g x))
  pr1 (extensionality-Π e g) = map-extensionality-Π e g
  pr2 (extensionality-Π e g) = is-equiv-map-extensionality-Π e g
```
