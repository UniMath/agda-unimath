---
title: Propositional maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-maps where

open import foundation-core.propositional-maps public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (_≃_)
open import foundation-core.propositions using (is-prop; UU-Prop)
open import foundation-core.truncation-levels using (neg-one-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.embeddings using (is-emb; is-emb-Prop)
open import foundation.logical-equivalences using (equiv-iff)
open import foundation.truncated-maps using (is-prop-is-trunc-map)
```

## Properties

### Being a propositional map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-prop-is-prop-map : (f : A → B) → is-prop (is-prop-map f)
  is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

  is-prop-map-Prop : (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-prop-map-Prop f) = is-prop-map f
  pr2 (is-prop-map-Prop f) = is-prop-is-prop-map f
```

### Being a propositional map is equivalent to being an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-emb-is-prop-map : (f : A → B) → is-prop-map f ≃ is-emb f
  equiv-is-emb-is-prop-map f =
    equiv-iff
      ( is-prop-map-Prop f)
      ( is-emb-Prop f)
      ( is-emb-is-prop-map)
      ( is-prop-map-is-emb)

  equiv-is-prop-map-is-emb : (f : A → B) → is-emb f ≃ is-prop-map f
  equiv-is-prop-map-is-emb f =
    equiv-iff
      ( is-emb-Prop f)
      ( is-prop-map-Prop f)
      ( is-prop-map-is-emb)
      ( is-emb-is-prop-map)
```
