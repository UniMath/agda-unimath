---
title: Transitive multisets
---

```agda
module trees.transitive-multisets where

open import foundation.equivalences
open import foundation.universe-levels

open import trees.multisets
```

## Idea

A multiset `x` is said to be transitive if for every `z ∈-𝕍 y ∈-𝕍 x` we have `z ∈-𝕍 x`.

## Definition

```agda
is-transitive-𝕍 : {l : Level} → 𝕍 l → UU (lsuc l)
is-transitive-𝕍 {l} x = (y z : 𝕍 l) → (y ∈-𝕍 x) → (z ∈-𝕍 y) ≃ (z ∈-𝕍 x)
```
