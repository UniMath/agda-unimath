---
title: Truncated types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-types where

open import foundation-core.truncated-types public

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import foundation.univalence
```

## Definition

### The subuniverse of truncated types

```agda
UU-Trunc : (k : 𝕋) (l : Level) → UU (lsuc l)
UU-Trunc k l = Σ (UU l) (is-trunc k)

type-UU-Trunc : {k : 𝕋} {l : Level} → UU-Trunc k l → UU l
type-UU-Trunc A = pr1 A

abstract
  is-trunc-type-UU-Trunc :
    {k : 𝕋} {l : Level} (A : UU-Trunc k l) → is-trunc k (type-UU-Trunc A)
  is-trunc-type-UU-Trunc A = pr2 A

abstract
  is-trunc-UU-Trunc :
    (k : 𝕋) {l : Level} → is-trunc (succ-𝕋 k) (UU-Trunc k l)
  is-trunc-UU-Trunc k X Y =
    is-trunc-is-equiv k
      ( pr1 X ＝ pr1 Y)
      ( ap pr1)
      ( is-emb-inclusion-subtype
        ( is-trunc-Prop k) X Y)
      ( is-trunc-is-equiv k
        ( (pr1 X) ≃ (pr1 Y))
        ( equiv-eq)
        ( univalence (pr1 X) (pr1 Y))
        ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))
```
