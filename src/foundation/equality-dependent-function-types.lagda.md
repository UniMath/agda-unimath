---
title: Equality on dependent function types
---

```agda
module foundation.equality-dependent-function-types where

open import foundation-core.dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation-core.contractible-types
open import foundation.type-theoretic-principle-of-choice
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
    ( (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
    ( g : (x : A) → B x) → f ＝ g → ((x : A) → Eq-B x (g x))
  map-extensionality-Π e .f refl x = map-equiv (e x (f x)) refl

  abstract
    is-equiv-map-extensionality-Π :
      (e : (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
      (g : (x : A) → B x) → is-equiv (map-extensionality-Π e g)
    is-equiv-map-extensionality-Π e =
      fundamental-theorem-id 
        ( is-contr-total-Eq-Π Eq-B
          ( λ x →
            fundamental-theorem-id'
              ( λ y → map-equiv (e x y))
              ( λ y → is-equiv-map-equiv (e x y))))
        ( map-extensionality-Π e)
  
  extensionality-Π :
    ( (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
    ( g : (x : A) → B x) → (f ＝ g) ≃ ((x : A) → Eq-B x (g x))
  pr1 (extensionality-Π e g) = map-extensionality-Π e g
  pr2 (extensionality-Π e g) = is-equiv-map-extensionality-Π e g
```
