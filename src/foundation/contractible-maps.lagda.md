---
title: Contractible maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.contractible-maps where

open import foundation-core.contractible-maps public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.truncation-levels using (neg-two-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.equivalences using (_≃_; is-equiv; is-equiv-Prop)
open import foundation.logical-equivalences using (equiv-iff)
open import foundation.propositions using (is-prop; Prop)
open import foundation.truncated-maps using (is-prop-is-trunc-map)
```

## Properties

### Being a contractible map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-prop-is-contr-map : (f : A → B) → is-prop (is-contr-map f)
  is-prop-is-contr-map f = is-prop-is-trunc-map neg-two-𝕋 f

  is-contr-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-contr-map-Prop f) = is-contr-map f
  pr2 (is-contr-map-Prop f) = is-prop-is-contr-map f
```

### Being a contractible map is equivalent to being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  equiv-is-equiv-is-contr-map : (f : A → B) → is-contr-map f ≃ is-equiv f
  equiv-is-equiv-is-contr-map f =
    equiv-iff
      ( is-contr-map-Prop f)
      ( is-equiv-Prop f)
      ( is-equiv-is-contr-map)
      ( is-contr-map-is-equiv)

  equiv-is-contr-map-is-equiv : (f : A → B) → is-equiv f ≃ is-contr-map f
  equiv-is-contr-map-is-equiv f =
    equiv-iff
      ( is-equiv-Prop f)
      ( is-contr-map-Prop f)
      ( is-contr-map-is-equiv)
      ( is-equiv-is-contr-map)
```
