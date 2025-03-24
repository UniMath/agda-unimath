# Fibers of directed graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.fibers-directed-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.equality-dependent-pair-types funext
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs funext univalence
open import graph-theory.morphisms-directed-graphs funext univalence truncations
open import graph-theory.walks-directed-graphs funext univalence truncations

open import trees.directed-trees funext univalence truncations
```

</details>

## Idea

Consider a vertex `x` in a [directed graph](graph-theory.directed-graphs.md)
`G`. The
{{#concept "fiber" Disambiguation="directed graph" Agda=fiber-Directed-Graph}}
of `G` at `x` is a [directed tree](trees.directed-trees.md) of which the type of
nodes consists of vertices `y` equipped with a
[walk](graph-theory.walks-directed-graphs.md) `w` from `y` to `x`, and the type
of edges from `(y , w)` to `(z , v)` consist of an edge `e : y → z` such that
`w ＝ cons e v`.

**Note:** The fiber of a directed graph should not be confused with the
[fiber of a morphism of directed graphs](graph-theory.fibers-morphisms-directed-graphs.md),
which is the
[dependent directed graph](graph-theory.dependent-directed-graphs.md) consisting
of the [fibers](foundation-core.fibers-of-maps.md) of the actions on vertices
and edges.

## Definitions

### The underlying graph of the fiber of `G` at `x`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  node-fiber-Directed-Graph : UU (l1 ⊔ l2)
  node-fiber-Directed-Graph =
    Σ (vertex-Directed-Graph G) (λ y → walk-Directed-Graph G y x)

  module _
    (u : node-fiber-Directed-Graph)
    where

    node-inclusion-fiber-Directed-Graph : vertex-Directed-Graph G
    node-inclusion-fiber-Directed-Graph = pr1 u

    walk-node-inclusion-fiber-Directed-Graph :
      walk-Directed-Graph G node-inclusion-fiber-Directed-Graph x
    walk-node-inclusion-fiber-Directed-Graph = pr2 u

  root-fiber-Directed-Graph : node-fiber-Directed-Graph
  pr1 root-fiber-Directed-Graph = x
  pr2 root-fiber-Directed-Graph = refl-walk-Directed-Graph

  is-root-fiber-Directed-Graph : node-fiber-Directed-Graph → UU (l1 ⊔ l2)
  is-root-fiber-Directed-Graph y = root-fiber-Directed-Graph ＝ y

  edge-fiber-Directed-Graph : (y z : node-fiber-Directed-Graph) → UU (l1 ⊔ l2)
  edge-fiber-Directed-Graph y z =
    Σ ( edge-Directed-Graph G
        ( node-inclusion-fiber-Directed-Graph y)
        ( node-inclusion-fiber-Directed-Graph z))
      ( λ e →
        ( walk-node-inclusion-fiber-Directed-Graph y) ＝
        ( cons-walk-Directed-Graph e
          ( walk-node-inclusion-fiber-Directed-Graph z)))

  module _
    (y z : node-fiber-Directed-Graph) (e : edge-fiber-Directed-Graph y z)
    where

    edge-inclusion-fiber-Directed-Graph :
      edge-Directed-Graph G
        ( node-inclusion-fiber-Directed-Graph y)
        ( node-inclusion-fiber-Directed-Graph z)
    edge-inclusion-fiber-Directed-Graph = pr1 e

    walk-edge-fiber-Directed-Graph :
      walk-node-inclusion-fiber-Directed-Graph y ＝
      cons-walk-Directed-Graph
        ( edge-inclusion-fiber-Directed-Graph)
        ( walk-node-inclusion-fiber-Directed-Graph z)
    walk-edge-fiber-Directed-Graph = pr2 e

  graph-fiber-Directed-Graph : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 graph-fiber-Directed-Graph = node-fiber-Directed-Graph
  pr2 graph-fiber-Directed-Graph = edge-fiber-Directed-Graph

  walk-fiber-Directed-Graph : (y z : node-fiber-Directed-Graph) → UU (l1 ⊔ l2)
  walk-fiber-Directed-Graph = walk-Directed-Graph graph-fiber-Directed-Graph

  walk-to-root-fiber-walk-Directed-Graph :
    (y : vertex-Directed-Graph G) (w : walk-Directed-Graph G y x) →
    walk-fiber-Directed-Graph (y , w) root-fiber-Directed-Graph
  walk-to-root-fiber-walk-Directed-Graph y refl-walk-Directed-Graph =
    refl-walk-Directed-Graph
  walk-to-root-fiber-walk-Directed-Graph .y
    ( cons-walk-Directed-Graph {y} {z} e w) =
    cons-walk-Directed-Graph
      ( e , refl)
      ( walk-to-root-fiber-walk-Directed-Graph z w)

  walk-to-root-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    walk-fiber-Directed-Graph y root-fiber-Directed-Graph
  walk-to-root-fiber-Directed-Graph (y , w) =
    walk-to-root-fiber-walk-Directed-Graph y w

  inclusion-fiber-Directed-Graph :
    hom-Directed-Graph graph-fiber-Directed-Graph G
  pr1 inclusion-fiber-Directed-Graph = node-inclusion-fiber-Directed-Graph
  pr2 inclusion-fiber-Directed-Graph = edge-inclusion-fiber-Directed-Graph
```

### The fiber of `G` at `x` as a directed tree

```agda
  center-unique-direct-successor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    ( is-root-fiber-Directed-Graph y) +
    ( Σ ( node-fiber-Directed-Graph) ( edge-fiber-Directed-Graph y))
  center-unique-direct-successor-fiber-Directed-Graph
    ( y , refl-walk-Directed-Graph) =
    inl refl
  center-unique-direct-successor-fiber-Directed-Graph
    ( y , cons-walk-Directed-Graph {y} {z} e w) = inr ((z , w) , (e , refl))

  contraction-unique-direct-successor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    ( p :
      ( is-root-fiber-Directed-Graph y) +
      ( Σ ( node-fiber-Directed-Graph) (edge-fiber-Directed-Graph y))) →
    center-unique-direct-successor-fiber-Directed-Graph y ＝ p
  contraction-unique-direct-successor-fiber-Directed-Graph ._ (inl refl) = refl
  contraction-unique-direct-successor-fiber-Directed-Graph
    ( y , .(cons-walk-Directed-Graph e v)) (inr ((z , v) , e , refl)) =
    refl

  unique-direct-successor-fiber-Directed-Graph :
    unique-direct-successor-Directed-Graph
      ( graph-fiber-Directed-Graph)
      ( root-fiber-Directed-Graph)
  pr1 (unique-direct-successor-fiber-Directed-Graph y) =
    center-unique-direct-successor-fiber-Directed-Graph y
  pr2 (unique-direct-successor-fiber-Directed-Graph y) =
    contraction-unique-direct-successor-fiber-Directed-Graph y

  is-tree-fiber-Directed-Graph :
    is-tree-Directed-Graph graph-fiber-Directed-Graph
  is-tree-fiber-Directed-Graph =
    is-tree-unique-direct-successor-Directed-Graph
      graph-fiber-Directed-Graph
      root-fiber-Directed-Graph
      unique-direct-successor-fiber-Directed-Graph
      walk-to-root-fiber-Directed-Graph

  fiber-Directed-Graph : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 fiber-Directed-Graph = graph-fiber-Directed-Graph
  pr2 fiber-Directed-Graph = is-tree-fiber-Directed-Graph
```

### Computing the direct predecessors of a node in a fiber

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) → UU (l1 ⊔ l2)
  direct-predecessor-fiber-Directed-Graph =
    direct-predecessor-Directed-Graph (graph-fiber-Directed-Graph G x)

  direct-predecessor-inclusion-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  direct-predecessor-inclusion-fiber-Directed-Graph =
    direct-predecessor-hom-Directed-Graph
      ( graph-fiber-Directed-Graph G x)
      ( G)
      ( inclusion-fiber-Directed-Graph G x)

  compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y ≃
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  compute-direct-predecessor-fiber-Directed-Graph y =
    ( right-unit-law-Σ-is-contr (λ (u , e) → is-torsorial-Id' _)) ∘e
    ( interchange-Σ-Σ _)

  map-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  map-compute-direct-predecessor-fiber-Directed-Graph y =
    map-equiv (compute-direct-predecessor-fiber-Directed-Graph y)

  htpy-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-inclusion-fiber-Directed-Graph y ~
    map-compute-direct-predecessor-fiber-Directed-Graph y
  htpy-compute-direct-predecessor-fiber-Directed-Graph y t = refl

  inv-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y) ≃
    direct-predecessor-fiber-Directed-Graph y
  inv-compute-direct-predecessor-fiber-Directed-Graph y =
    inv-equiv (compute-direct-predecessor-fiber-Directed-Graph y)

  Eq-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    (u v : direct-predecessor-fiber-Directed-Graph y) → UU (l1 ⊔ l2)
  Eq-direct-predecessor-fiber-Directed-Graph y u v =
    Σ ( pr1 (direct-predecessor-inclusion-fiber-Directed-Graph y u) ＝
        pr1 (direct-predecessor-inclusion-fiber-Directed-Graph y v))
      ( λ p →
        tr
          ( λ t →
            edge-Directed-Graph G t (node-inclusion-fiber-Directed-Graph G x y))
          ( p)
          ( pr2 (direct-predecessor-inclusion-fiber-Directed-Graph y u)) ＝
            pr2 (direct-predecessor-inclusion-fiber-Directed-Graph y v))

  eq-Eq-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    ( u v : direct-predecessor-fiber-Directed-Graph y) →
    Eq-direct-predecessor-fiber-Directed-Graph y u v → u ＝ v
  eq-Eq-direct-predecessor-fiber-Directed-Graph y u v p =
    map-inv-equiv
      ( equiv-ap (compute-direct-predecessor-fiber-Directed-Graph y) u v)
      ( eq-pair-Σ' p)
```
