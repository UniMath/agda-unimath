---
title: The underlying graphs of elements of W-types
---

```agda
module foundation.underlying-graphs-of-elements-w-types where

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.elementhood-relation-w-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.w-types
```

## Idea

We assign to each element of a W-type `𝕎 A B` a directed graph. This directed graph is a tree in the graph theoretical sense if and only if each `B x` is a type with decidable equality.


## Definition

### The type of nodes of the underlying graph of an element of a W-type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data node-graph-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root-𝕎 :
      {w : 𝕎 A B} → node-graph-element-𝕎 w
    node-𝕎 :
      (u v : 𝕎 A B) → (u ∈-𝕎 v) →
      node-graph-element-𝕎 u → node-graph-element-𝕎 v

  data edge-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) → UU (l1 ⊔ l2)
    where
    edge-to-root-graph-element-𝕎 :
      (u v : 𝕎 A B) (H : u ∈-𝕎 v) →
      edge-graph-element-𝕎 v (node-𝕎 u v H root-𝕎) root-𝕎
    edge-to-node-graph-element-𝕎 :
      (u v : 𝕎 A B) (H : u ∈-𝕎 v) →
      {x y : node-graph-element-𝕎 u} (e : edge-graph-element-𝕎 u x y) →
      edge-graph-element-𝕎 v (node-𝕎 u v H x) (node-𝕎 u v H y)
```
