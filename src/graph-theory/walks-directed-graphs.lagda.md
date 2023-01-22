---
title: Walks in directed graphs
---

```agda
module graph-theory.walks-directed-graphs where

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

## Idea

A walk in a directed graph from a vertex `x` to a vertex `y` is a list of edges that connect `x` to `y`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2) (x : vertex-Graph G)
  where

  data walk-Graph : vertex-Graph G → UU (l1 ⊔ l2) where
    refl-walk-Graph : walk-Graph x
    cons-walk-Graph :
      {y z : vertex-Graph G} → walk-Graph y → edge-Graph G y z → walk-Graph z
```

## Properties

### Vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2) {x : vertex-Graph G}
  where

  is-vertex-on-walk-Graph :
    {y : vertex-Graph G} (w : walk-Graph G x y) (v : vertex-Graph G) → UU l1
  is-vertex-on-walk-Graph refl-walk-Graph v = v ＝ x
  is-vertex-on-walk-Graph (cons-walk-Graph {y} {z} w e) v =
    ( is-vertex-on-walk-Graph w v) +
    ( v ＝ z)

  vertex-on-walk-Graph : {y : vertex-Graph G} (w : walk-Graph G x y) → UU l1
  vertex-on-walk-Graph w = Σ (vertex-Graph G) (is-vertex-on-walk-Graph w)

  vertex-vertex-on-walk-Graph :
    {y : vertex-Graph G} (w : walk-Graph G x y) →
    vertex-on-walk-Graph w → vertex-Graph G
  vertex-vertex-on-walk-Graph w = pr1
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2) {x : vertex-Graph G}
  where

  data is-edge-on-walk-Graph :
    {y : vertex-Graph G} (w : walk-Graph G x y)
    {u v : vertex-Graph G} → edge-Graph G u v → UU (l1 ⊔ l2)
    where
    cons-is-edge-on-walk-Graph :
      {y z : vertex-Graph G} (w : walk-Graph G x y) (e : edge-Graph G y z) →
      {u v : vertex-Graph G} (f : edge-Graph G u v) → 
      is-edge-on-walk-Graph w f →
      is-edge-on-walk-Graph (cons-walk-Graph w e) f
    edge-is-edge-on-walk-Graph :
      {y z : vertex-Graph G} (w : walk-Graph G x y) (e : edge-Graph G y z) →
      is-edge-on-walk-Graph (cons-walk-Graph w e) e

  edge-on-walk-Graph :
    {y : vertex-Graph G} (w : walk-Graph G x y) → UU (l1 ⊔ l2)
  edge-on-walk-Graph w =
    Σ ( total-edge-Graph G)
      ( λ e → is-edge-on-walk-Graph w (edge-total-edge-Graph G e))

  module _
    {y : vertex-Graph G} (w : walk-Graph G x y) (e : edge-on-walk-Graph w)
    where

    total-edge-edge-on-walk-Graph : total-edge-Graph G
    total-edge-edge-on-walk-Graph = pr1 e
    
    source-edge-on-walk-Graph : vertex-Graph G
    source-edge-on-walk-Graph =
      source-total-edge-Graph G total-edge-edge-on-walk-Graph

    target-edge-on-walk-Graph : vertex-Graph G
    target-edge-on-walk-Graph =
      target-total-edge-Graph G total-edge-edge-on-walk-Graph

    edge-edge-on-walk-Graph :
      edge-Graph G source-edge-on-walk-Graph target-edge-on-walk-Graph
    edge-edge-on-walk-Graph =
      edge-total-edge-Graph G total-edge-edge-on-walk-Graph

    is-edge-on-walk-edge-on-walk-Graph :
      is-edge-on-walk-Graph w edge-edge-on-walk-Graph
    is-edge-on-walk-edge-on-walk-Graph = pr2 e
```

### The action on walks of graph homomorphisms

```agda
walk-hom-Graph :
  {l1 l2 l3 l4 : Level} (G : Graph l1 l2) (H : Graph l3 l4)
  (f : hom-Graph G H) {x y : vertex-Graph G} →
  walk-Graph G x y →
  walk-Graph H (vertex-hom-Graph G H f x) (vertex-hom-Graph G H f y)
walk-hom-Graph G H f refl-walk-Graph = refl-walk-Graph
walk-hom-Graph G H f (cons-walk-Graph w e) =
  cons-walk-Graph (walk-hom-Graph G H f w) (edge-hom-Graph G H f e)
```
