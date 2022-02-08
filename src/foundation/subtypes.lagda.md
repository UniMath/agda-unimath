# Subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtypes where

open import foundation-core.subtypes public

open import foundation-core.dependent-pair-types using (Σ)
open import foundation-core.equivalences using (_≃_; map-equiv)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-Σ)
open import foundation-core.propositions using (UU-Prop; type-Prop)
open import foundation-core.truncation-levels using (𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU)

open import foundation-core.logical-equivalences using (_↔_; equiv-iff')
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
