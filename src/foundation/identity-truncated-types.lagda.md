---
title: Identity types of truncated types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.identity-truncated-types where

open import foundation-core.equivalences using (_≃_)
open import foundation-core.truncation-levels using (𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.identity-types using (_＝_)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-equiv; is-trunc-equiv-is-trunc)
open import foundation.univalence using (equiv-univalence)

```

### The type of identity of truncated types is truncated

```agda
module _
  {l : Level} {A B : UU l}
  where

  is-trunc-id-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ＝ B)
  is-trunc-id-is-trunc k is-trunc-A is-trunc-B =
    is-trunc-equiv k
      ( A ≃ B)
      ( equiv-univalence)
      ( is-trunc-equiv-is-trunc k is-trunc-A is-trunc-B)
```
