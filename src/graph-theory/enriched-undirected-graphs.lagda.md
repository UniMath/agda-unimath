# Enriched undirected graphs

```agda
module graph-theory.enriched-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs

open import higher-group-theory.higher-group-actions
open import higher-group-theory.higher-groups
```

</details>

## Idea

Consider a type `A` equipped with a type family `B` over `A`. An
`(A,B)`-{{#concept "enriched undirected graph" Agda=Enriched-Undirected-Graph}}
is an [undirected graph](graph-theory.undirected-graphs.md) `G := (V,E)`
equipped with a map `sh : V → A`, and for each vertex `v` an
[equivalence](foundation-core.equivalences.md) from `B (sh v)` to the type of
all edges going out of `v`, i.e., to the type `neighbor v` of
[neighbors](graph-theory.neighbors-undirected-graphs.md).

The map `sh : V → A` assigns to each vertex a shape, and with it an
[∞-group](higher-group-theory.higher-groups.md) `BAut (sh v)`. The type family
`B` restricted to `BAut (sh v)` is an
[`Aut (sh v)`-type](higher-group-theory.higher-group-actions.md), and the
equivalence `B (sh v) ≃ neighbor v` then ensures type type being acted on is
`neighbor v`.

## Definition

```agda
Enriched-Undirected-Graph :
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Enriched-Undirected-Graph l3 l4 A B =
  Σ ( Undirected-Graph l3 l4)
    ( λ G →
      Σ ( vertex-Undirected-Graph G → A)
        ( λ f →
          ( x : vertex-Undirected-Graph G) →
          B (f x) ≃ neighbor-Undirected-Graph G x))

module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  where

  undirected-graph-Enriched-Undirected-Graph : Undirected-Graph l3 l4
  undirected-graph-Enriched-Undirected-Graph = pr1 G

  vertex-Enriched-Undirected-Graph : UU l3
  vertex-Enriched-Undirected-Graph =
    vertex-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  unordered-pair-vertices-Enriched-Undirected-Graph : UU (lsuc lzero ⊔ l3)
  unordered-pair-vertices-Enriched-Undirected-Graph =
    unordered-pair-vertices-Undirected-Graph
      undirected-graph-Enriched-Undirected-Graph

  edge-Enriched-Undirected-Graph :
    unordered-pair-vertices-Enriched-Undirected-Graph → UU l4
  edge-Enriched-Undirected-Graph =
    edge-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  shape-vertex-Enriched-Undirected-Graph : vertex-Enriched-Undirected-Graph → A
  shape-vertex-Enriched-Undirected-Graph = pr1 (pr2 G)

  classifying-type-∞-group-vertex-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph → UU l1
  classifying-type-∞-group-vertex-Enriched-Undirected-Graph v =
    connected-component A (shape-vertex-Enriched-Undirected-Graph v)

  point-classifying-type-∞-group-vertex-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    classifying-type-∞-group-vertex-Enriched-Undirected-Graph v
  point-classifying-type-∞-group-vertex-Enriched-Undirected-Graph v =
    point-connected-component A (shape-vertex-Enriched-Undirected-Graph v)

  ∞-group-vertex-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph → ∞-Group l1
  ∞-group-vertex-Enriched-Undirected-Graph v =
    connected-component-∞-Group A (shape-vertex-Enriched-Undirected-Graph v)

  type-∞-group-vertex-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph → UU l1
  type-∞-group-vertex-Enriched-Undirected-Graph v =
    type-∞-Group (∞-group-vertex-Enriched-Undirected-Graph v)

  mul-∞-group-vertex-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    (h g : type-∞-group-vertex-Enriched-Undirected-Graph v) →
    type-∞-group-vertex-Enriched-Undirected-Graph v
  mul-∞-group-vertex-Enriched-Undirected-Graph v h g =
    mul-∞-Group (∞-group-vertex-Enriched-Undirected-Graph v) h g

  neighbor-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph → UU (l3 ⊔ l4)
  neighbor-Enriched-Undirected-Graph =
    neighbor-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  equiv-neighbor-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    B (shape-vertex-Enriched-Undirected-Graph v) ≃
    neighbor-Enriched-Undirected-Graph v
  equiv-neighbor-Enriched-Undirected-Graph = pr2 (pr2 G)

  map-equiv-neighbor-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    B (shape-vertex-Enriched-Undirected-Graph v) →
    neighbor-Enriched-Undirected-Graph v
  map-equiv-neighbor-Enriched-Undirected-Graph v =
    map-equiv (equiv-neighbor-Enriched-Undirected-Graph v)

  map-inv-equiv-neighbor-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    neighbor-Enriched-Undirected-Graph v →
    B (shape-vertex-Enriched-Undirected-Graph v)
  map-inv-equiv-neighbor-Enriched-Undirected-Graph v =
    map-inv-equiv (equiv-neighbor-Enriched-Undirected-Graph v)

  is-section-map-inv-equiv-neighbor-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    ( map-equiv-neighbor-Enriched-Undirected-Graph v ∘
      map-inv-equiv-neighbor-Enriched-Undirected-Graph v) ~ id
  is-section-map-inv-equiv-neighbor-Enriched-Undirected-Graph v =
    is-section-map-inv-equiv (equiv-neighbor-Enriched-Undirected-Graph v)

  is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    ( map-inv-equiv-neighbor-Enriched-Undirected-Graph v ∘
      map-equiv-neighbor-Enriched-Undirected-Graph v) ~ id
  is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graph v =
    is-retraction-map-inv-equiv (equiv-neighbor-Enriched-Undirected-Graph v)

  action-∞-group-vertex-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph) →
    action-∞-Group l2 (∞-group-vertex-Enriched-Undirected-Graph v)
  action-∞-group-vertex-Enriched-Undirected-Graph v u = B (pr1 u)

  mul-action-∞-group-vertex-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph)
    (g : type-∞-group-vertex-Enriched-Undirected-Graph v) →
    neighbor-Enriched-Undirected-Graph v → neighbor-Enriched-Undirected-Graph v
  mul-action-∞-group-vertex-Enriched-Undirected-Graph v g e =
    map-equiv-neighbor-Enriched-Undirected-Graph v
      ( mul-action-∞-Group
        ( ∞-group-vertex-Enriched-Undirected-Graph v)
        ( action-∞-group-vertex-Enriched-Undirected-Graph v)
        ( g)
        ( map-inv-equiv-neighbor-Enriched-Undirected-Graph v e))

  associative-mul-action-∞-group-vertex-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph)
    (h g : type-∞-group-vertex-Enriched-Undirected-Graph v) →
    (x : neighbor-Enriched-Undirected-Graph v) →
    ( mul-action-∞-group-vertex-Enriched-Undirected-Graph v
      ( mul-∞-group-vertex-Enriched-Undirected-Graph v h g)
      ( x)) ＝
    ( mul-action-∞-group-vertex-Enriched-Undirected-Graph v g
      ( mul-action-∞-group-vertex-Enriched-Undirected-Graph v h x))
  associative-mul-action-∞-group-vertex-Enriched-Undirected-Graph v h g x =
    ap
      ( map-equiv-neighbor-Enriched-Undirected-Graph v)
      ( ( associative-mul-action-∞-Group
          ( ∞-group-vertex-Enriched-Undirected-Graph v)
          ( action-∞-group-vertex-Enriched-Undirected-Graph v)
          ( h)
          ( g)
          ( map-inv-equiv-neighbor-Enriched-Undirected-Graph v x)) ∙
        ( ap
          ( mul-action-∞-Group
            ( ∞-group-vertex-Enriched-Undirected-Graph v)
            ( action-∞-group-vertex-Enriched-Undirected-Graph v)
            ( g))
          ( inv
            ( is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graph v
              ( mul-action-∞-Group
                ( ∞-group-vertex-Enriched-Undirected-Graph v)
                ( action-∞-group-vertex-Enriched-Undirected-Graph v) h
                ( map-inv-equiv-neighbor-Enriched-Undirected-Graph v x))))))
```

## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Graph](https://mathworld.wolfram.com/Graph.html) at Wolfram MathWorld
