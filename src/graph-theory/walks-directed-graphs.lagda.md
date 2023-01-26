---
title: Walks in directed graphs
---

```agda
module graph-theory.walks-directed-graphs where

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
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
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  data walk-Graph : (x y : vertex-Graph G) → UU (l1 ⊔ l2) where
    refl-walk-Graph :
      {x : vertex-Graph G} → walk-Graph x x
    cons-walk-Graph :
      {x y z : vertex-Graph G} →
      edge-Graph G x y →  walk-Graph y z → walk-Graph x z
```

## Properties

### The type of walks from `x` to `y` is a coproduct

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  walk-Graph' : (x y : vertex-Graph G) → UU (l1 ⊔ l2)
  walk-Graph' x y =
    (x ＝ y) + Σ (vertex-Graph G) (λ z → edge-Graph G x z × walk-Graph G z y)

  map-compute-walk-Graph :
    (x y : vertex-Graph G) → walk-Graph G x y → walk-Graph' x y
  map-compute-walk-Graph x .x refl-walk-Graph = inl refl
  map-compute-walk-Graph x y (cons-walk-Graph {a} {b} {c} e w) = inr (b , e , w)

  map-inv-compute-walk-Graph :
    (x y : vertex-Graph G) → walk-Graph' x y → walk-Graph G x y
  map-inv-compute-walk-Graph x .x (inl refl) = refl-walk-Graph
  map-inv-compute-walk-Graph x y (inr (z , e , w)) = cons-walk-Graph e w

  issec-map-inv-compute-walk-Graph :
    (x y : vertex-Graph G) →
    ( map-compute-walk-Graph x y ∘ map-inv-compute-walk-Graph x y) ~ id
  issec-map-inv-compute-walk-Graph x .x (inl refl) = refl
  issec-map-inv-compute-walk-Graph x y (inr (z , e , w)) = refl

  isretr-map-inv-compute-walk-Graph :
    (x y : vertex-Graph G) →
    ( map-inv-compute-walk-Graph x y ∘ map-compute-walk-Graph x y) ~ id
  isretr-map-inv-compute-walk-Graph x .x refl-walk-Graph = refl
  isretr-map-inv-compute-walk-Graph x y (cons-walk-Graph e w) = refl

  is-equiv-map-compute-walk-Graph :
    (x y : vertex-Graph G) → is-equiv (map-compute-walk-Graph x y)
  is-equiv-map-compute-walk-Graph x y =
    is-equiv-has-inverse
      ( map-inv-compute-walk-Graph x y)
      ( issec-map-inv-compute-walk-Graph x y)
      ( isretr-map-inv-compute-walk-Graph x y)

  compute-walk-Graph :
    (x y : vertex-Graph G) → walk-Graph G x y ≃ walk-Graph' x y
  pr1 (compute-walk-Graph x y) = map-compute-walk-Graph x y
  pr2 (compute-walk-Graph x y) = is-equiv-map-compute-walk-Graph x y
```

### Vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  is-vertex-on-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y) (v : vertex-Graph G) → UU l1
  is-vertex-on-walk-Graph {x} refl-walk-Graph v = v ＝ x
  is-vertex-on-walk-Graph {x} (cons-walk-Graph e w) v =
    ( v ＝ x) +
    ( is-vertex-on-walk-Graph w v)

  vertex-on-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y) → UU l1
  vertex-on-walk-Graph w = Σ (vertex-Graph G) (is-vertex-on-walk-Graph w)

  vertex-vertex-on-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y) →
    vertex-on-walk-Graph w → vertex-Graph G
  vertex-vertex-on-walk-Graph w = pr1
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  data is-edge-on-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y)
    {u v : vertex-Graph G} → edge-Graph G u v → UU (l1 ⊔ l2)
    where
    edge-is-edge-on-walk-Graph :
      {x y z : vertex-Graph G} (e : edge-Graph G x y) (w : walk-Graph G y z) →
      is-edge-on-walk-Graph (cons-walk-Graph e w) e
    cons-is-edge-on-walk-Graph :
      {x y z : vertex-Graph G} (e : edge-Graph G x y) (w : walk-Graph G y z) →
      {u v : vertex-Graph G} (f : edge-Graph G u v) →
      is-edge-on-walk-Graph w f →
      is-edge-on-walk-Graph (cons-walk-Graph e w) f

  edge-on-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y) → UU (l1 ⊔ l2)
  edge-on-walk-Graph w =
    Σ ( total-edge-Graph G)
      ( λ e → is-edge-on-walk-Graph w (edge-total-edge-Graph G e))

  module _
    {x y : vertex-Graph G} (w : walk-Graph G x y) (e : edge-on-walk-Graph w)
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
walk-hom-Graph G H f (cons-walk-Graph e w) =
  cons-walk-Graph (edge-hom-Graph G H f e) (walk-hom-Graph G H f w)
```
