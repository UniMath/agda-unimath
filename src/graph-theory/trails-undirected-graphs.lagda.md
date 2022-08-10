---
title: Trails in undirected graphs
---

```agda
module graph-theory.trails-undirected-graphs where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.injective-maps
open import foundation.universe-levels

open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

## Idea

A trail in an undirected graph is a walk that passes through each edge at most once

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where
  
  is-trail-walk-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-trail-walk-Undirected-Graph w =
    is-injective (edge-edge-on-walk-Undirected-Graph G w)

  trail-Undirected-Graph :
    (x y : vertex-Undirected-Graph G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  trail-Undirected-Graph x y =
    Σ (walk-Undirected-Graph G x y) is-trail-walk-Undirected-Graph

  walk-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} →
    trail-Undirected-Graph x y → walk-Undirected-Graph G x y
  walk-trail-Undirected-Graph = pr1

  is-vertex-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} →
    trail-Undirected-Graph x y → vertex-Undirected-Graph G → UU l1
  is-vertex-on-trail-Undirected-Graph t =
    is-vertex-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  vertex-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → trail-Undirected-Graph x y → UU l1
  vertex-on-trail-Undirected-Graph t =
    vertex-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  vertex-vertex-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph x y) →
    vertex-on-trail-Undirected-Graph t → vertex-Undirected-Graph G
  vertex-vertex-on-trail-Undirected-Graph t =
    vertex-vertex-on-walk-Undirected-Graph G
      ( walk-trail-Undirected-Graph t)

  length-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → trail-Undirected-Graph x y → ℕ
  length-trail-Undirected-Graph t =
    length-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)
```

## Properties

### Any constant walk is a trail

```agda
is-trail-refl-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G} →
  is-trail-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x})
is-trail-refl-walk-Undirected-Graph G {x} =
  is-injective-is-empty
    ( edge-edge-on-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x}))
    ( is-empty-edge-on-walk-refl-walk-Undirected-Graph G x)
```

### Both walks in the decomposition of a trail are trails

Note that in general, the concatenation of two trails does not need to be a trail.

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  first-segment-trail-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph G x y)
    (v : vertex-on-trail-Undirected-Graph G t) →
    walk-Undirected-Graph G x
      ( vertex-vertex-on-trail-Undirected-Graph G t v)
  first-segment-trail-Undirected-Graph t =
    first-segment-walk-Undirected-Graph G
      ( walk-trail-Undirected-Graph G t)

  second-segment-trail-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph G x y)
    (v : vertex-on-trail-Undirected-Graph G t) →
    walk-Undirected-Graph G
      ( vertex-vertex-on-trail-Undirected-Graph G t v)
      ( y)
  second-segment-trail-Undirected-Graph t =
    second-segment-walk-Undirected-Graph G
      ( walk-trail-Undirected-Graph G t)
{-
  is-trail-first-walk-decomposition-trail-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph G t)) →
    is-trail-walk-Undirected-Graph G
      ( first-segment-trail-Undirected-Graph t v)
  is-trail-first-walk-decomposition-trail-Undirected-Graph = {!!}
  -}
```
