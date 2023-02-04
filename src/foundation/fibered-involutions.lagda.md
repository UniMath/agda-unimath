---
title: Fibered involutions
---

```agda
module foundation.fibered-involutions where

open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.involutions
open import foundation-core.universe-levels

open import foundation.fibered-maps
```

## Idea

A fibered involution is a fibered map

```md
       h
  A -------> A
  |          |
 f|          |g
  |          |
  V          V
  X -------> X
       i
```

such that both `i` and `h` are involutions.

## Definition

```agda
involution-over :
  {l1 l2 l3 : Level} {A : UU l1} {X : UU l2} {Y : UU l3} →
  (A → X) → (A → Y) → (X → Y) → UU (l1 ⊔ l3)
involution-over {A = A} f g i = Σ (involution A) (is-map-over f g i ∘ map-involution)

fibered-involution :
  {l1 l2 : Level} {A : UU l1} {X : UU l2} →
  (A → X) → (A → X) → UU (l1 ⊔ l2)
fibered-involution {X = X} f g = Σ (involution X) (involution-over f g ∘ map-involution)

is-fiberwise-involution : 
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  ((x : X) → P x → P x) → UU (l1 ⊔ l2)
is-fiberwise-involution {X = X} f = (x : X) → is-involution (f x)

fam-involution : 
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) → UU (l1 ⊔ l2)
fam-involution {X = X} P = (x : X) → involution (P x)
```
