---
title: Connected maps
---

```agda
module foundation.connected-maps where

open import foundation.connected-types
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.universe-levels
```

## Idea

A map is said to be **`k`-connected** if its fibers are `k`-connected types.

## Definition

```agda
is-connected-map-Prop :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-connected-map-Prop k {B = B} f =
  Π-Prop B (λ b → is-connected-Prop k (fib f b))

is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-connected-map k f = type-Prop (is-connected-map-Prop k f)

is-prop-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-connected-map k f)
is-prop-is-connected-map k f = is-prop-type-Prop (is-connected-map-Prop k f)
```
