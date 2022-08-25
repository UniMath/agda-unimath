---
title: Truncated types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-types where

open import foundation-core.truncated-types public

open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import foundation.subtype-identity-principle
open import foundation.univalence
```

## Definition

### The subuniverse of truncated types is itself truncated

```agda
extensionality-Truncated-Type :
  {l : Level} {k : 𝕋} (A B : Truncated-Type l k) →
  (A ＝ B) ≃ type-equiv-Truncated-Type A B
extensionality-Truncated-Type A =
  extensionality-type-subtype
    ( is-trunc-Prop _)
    ( is-trunc-type-Truncated-Type A)
    ( id-equiv)
    ( λ X → equiv-univalence)

abstract
  is-trunc-Truncated-Type :
    {l : Level} (k : 𝕋) → is-trunc (succ-𝕋 k) (Truncated-Type l k)
  is-trunc-Truncated-Type k X Y =
    is-trunc-equiv k
      ( type-equiv-Truncated-Type X Y)
      ( extensionality-Truncated-Type X Y)
      ( is-trunc-type-equiv-Truncated-Type X Y)

Truncated-Type-Truncated-Type :
  (l : Level) (k : 𝕋) → Truncated-Type (lsuc l) (succ-𝕋 k)
pr1 (Truncated-Type-Truncated-Type l k) = Truncated-Type l k
pr2 (Truncated-Type-Truncated-Type l k) = is-trunc-Truncated-Type k
```

### The embedding of the subuniverse of truncated types into the universe

```agda
emb-type-Truncated-Type : (l : Level) (k : 𝕋) → Truncated-Type l k ↪ UU l
emb-type-Truncated-Type l k = emb-subtype (is-trunc-Prop k)
```
