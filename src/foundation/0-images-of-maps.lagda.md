---
title: 0-Images of maps
---

```agda
module foundation.0-images-of-maps where

open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.universe-levels
```

## Idea

The 0-image of a map `f : A → B` is the type `0-im f := Σ (b : B), type-trunc-Set (fib f b)`. The map `A → 0-im f` is 0-connected and the map `0-im f → B` is `0`-truncated.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  0-im : UU (l1 ⊔ l2)
  0-im = Σ B (λ b → type-trunc-Set (fib f b))

  unit-0-im : A → 0-im
  pr1 (unit-0-im x) = f x
  pr2 (unit-0-im x) = unit-trunc-Set (pair x refl)

  projection-0-im : 0-im → B
  projection-0-im = pr1
```
