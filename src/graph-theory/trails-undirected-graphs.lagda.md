# Trails in undirected graphs

```agda
module graph-theory.trails-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

</details>

## Idea

A
{{#concept "trail" Disambiguation="in an undirected graph" WD="trail" WDID=Q17455228 Agda=trail-Undirected-Graph}}
in an [undirected graph](graph-theory.undirected-graphs.md) is a
[walk](graph-theory.walks-undirected-graphs.md) that passes through each edge at
most once.

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

  is-trail-walk-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph x y) →
    is-trail-walk-Undirected-Graph (walk-trail-Undirected-Graph t)
  is-trail-walk-trail-Undirected-Graph = pr2

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

  is-edge-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} →
    (t : trail-Undirected-Graph x y)
    (p : unordered-pair-vertices-Undirected-Graph G)
    (e : edge-Undirected-Graph G p) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-trail-Undirected-Graph t =
    is-edge-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  edge-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph x y) →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-trail-Undirected-Graph t =
    edge-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  edge-edge-on-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph x y) →
    edge-on-trail-Undirected-Graph t → total-edge-Undirected-Graph G
  edge-edge-on-trail-Undirected-Graph t =
    edge-edge-on-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  length-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → trail-Undirected-Graph x y → ℕ
  length-trail-Undirected-Graph t =
    length-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  is-constant-trail-Undirected-Graph-Prop :
    {x y : vertex-Undirected-Graph G} →
    trail-Undirected-Graph x y → Prop lzero
  is-constant-trail-Undirected-Graph-Prop t =
    is-constant-walk-Undirected-Graph-Prop G (walk-trail-Undirected-Graph t)

  is-constant-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → trail-Undirected-Graph x y → UU lzero
  is-constant-trail-Undirected-Graph t =
    is-constant-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)

  is-decidable-is-constant-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} (t : trail-Undirected-Graph x y) →
    is-decidable (is-constant-trail-Undirected-Graph t)
  is-decidable-is-constant-trail-Undirected-Graph t =
    is-decidable-is-constant-walk-Undirected-Graph G
      ( walk-trail-Undirected-Graph t)
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

Note that in general, the concatenation of two trails does not need to be a
trail.

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
```

## External links

- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Trail](https://www.wikidata.org/entity/Q17455228) on Wikidata
- [Trail](https://mathworld.wolfram.com/Trail.html) at Wolfram MathWorld
