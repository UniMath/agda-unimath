# Subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtypes where

open import foundation-core.subtypes public

open import foundation-core.dependent-pair-types using (Σ)
open import foundation-core.equivalences using
  ( _≃_; map-equiv; is-equiv; map-inv-is-equiv; isretr-map-inv-is-equiv)
open import foundation-core.functions using (_∘_)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-Σ; map-Σ; is-equiv-map-Σ)
open import foundation-core.identity-types using (tr)
open import foundation-core.logical-equivalences using (_↔_; equiv-iff')
open import foundation-core.propositions using
  ( UU-Prop; type-Prop; is-equiv-is-prop)
open import foundation-core.truncation-levels using (𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU)
```

### Equivalences of subtypes

```agda
equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  type-subtype C ≃ type-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))
```

```agda
abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' {P = P} {Q}
    is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
        ( (tr P (isretr-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))
```
