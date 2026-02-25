# Fibers of morphisms into directed graphs

```agda
module graph-theory.fibers-morphisms-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.dependent-sums-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.equivalences-dependent-directed-graphs
open import graph-theory.equivalences-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

Consider a [morphism](graph-theory.morphisms-directed-graphs.md) `f : H → G` of
[directed graphs](graph-theory.directed-graphs.md). The
{{#concept "fiber" Disambiguation="morphisms of directed graphs" Agda=fiber-hom-Directed-Graph}}
of `f` is the
[dependent directed graph](graph-theory.dependent-directed-graphs.md) `fib_f`
over `G` given by

```text
  (fib_f)₀ x := fib f₀
  (fib_f)₁ e (y , refl) (y' , refl) := fib f₁ e.
```

**Note:** The fiber of a morphism of directed graphs should not be confused with
the
[fiber of a directed graph at a vertex](graph-theory.fibers-directed-graphs.md),
which are the [directed trees](trees.directed-trees.md) of which the type of
nodes consists of vertices `y` equipped with a
[walk](graph-theory.walks-directed-graphs.md) `w` from `y` to `x`, and the type
of edges from `(y , w)` to `(z , v)` consist of an edge `e : y → z` such that
`w ＝ cons e v`.

## Definitions

### The fiber of a morphism of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Directed-Graph l1 l2) (G : Directed-Graph l3 l4)
  (f : hom-Directed-Graph H G)
  where

  vertex-fiber-hom-Directed-Graph :
    vertex-Directed-Graph G → UU (l1 ⊔ l3)
  vertex-fiber-hom-Directed-Graph = fiber (vertex-hom-Directed-Graph H G f)

  edge-fiber-hom-Directed-Graph :
    {x x' : vertex-Directed-Graph G} →
    edge-Directed-Graph G x x' →
    vertex-fiber-hom-Directed-Graph x →
    vertex-fiber-hom-Directed-Graph x' → UU (l2 ⊔ l4)
  edge-fiber-hom-Directed-Graph e (y , refl) (y' , refl) =
    fiber (edge-hom-Directed-Graph H G f) e

  fiber-hom-Directed-Graph : Dependent-Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  pr1 fiber-hom-Directed-Graph = vertex-fiber-hom-Directed-Graph
  pr2 fiber-hom-Directed-Graph _ _ = edge-fiber-hom-Directed-Graph
```

## Properties

### The coproduct of the fibers of a morphism of directed graphs is the equivalent to the codomain

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Directed-Graph l1 l2) (G : Directed-Graph l3 l4)
  (f : hom-Directed-Graph H G)
  where

  vertex-compute-Σ-fiber-hom-Directed-Graph :
    vertex-Directed-Graph H ≃
    vertex-Σ-Directed-Graph (fiber-hom-Directed-Graph H G f)
  vertex-compute-Σ-fiber-hom-Directed-Graph =
    inv-equiv-total-fiber (vertex-hom-Directed-Graph H G f)

  map-vertex-compute-Σ-fiber-hom-Directed-Graph :
    vertex-Directed-Graph H →
    vertex-Σ-Directed-Graph (fiber-hom-Directed-Graph H G f)
  map-vertex-compute-Σ-fiber-hom-Directed-Graph =
    map-equiv vertex-compute-Σ-fiber-hom-Directed-Graph

  edge-compute-Σ-fiber-hom-Directed-Graph :
    {x y : vertex-Directed-Graph H} →
    edge-Directed-Graph H x y ≃
    edge-Σ-Directed-Graph
      ( fiber-hom-Directed-Graph H G f)
      ( map-vertex-compute-Σ-fiber-hom-Directed-Graph x)
      ( map-vertex-compute-Σ-fiber-hom-Directed-Graph y)
  edge-compute-Σ-fiber-hom-Directed-Graph =
    inv-equiv-total-fiber (edge-hom-Directed-Graph H G f)

  compute-Σ-fiber-hom-Directed-Graph :
    equiv-Directed-Graph H (Σ-Directed-Graph (fiber-hom-Directed-Graph H G f))
  pr1 compute-Σ-fiber-hom-Directed-Graph =
    vertex-compute-Σ-fiber-hom-Directed-Graph
  pr2 compute-Σ-fiber-hom-Directed-Graph _ _ =
    edge-compute-Σ-fiber-hom-Directed-Graph

  hom-compute-Σ-fiber-hom-Directed-Graph :
    hom-Directed-Graph H (Σ-Directed-Graph (fiber-hom-Directed-Graph H G f))
  hom-compute-Σ-fiber-hom-Directed-Graph =
    hom-equiv-Directed-Graph H
      ( Σ-Directed-Graph (fiber-hom-Directed-Graph H G f))
      ( compute-Σ-fiber-hom-Directed-Graph)
```

### The equivalence of the domain and the total graph of the fibers of a morphism of graphs fits in a commuting triangle

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Directed-Graph l1 l2) (G : Directed-Graph l3 l4)
  (f : hom-Directed-Graph H G)
  where

  htpy-compute-Σ-fiber-hom-Directed-Graph :
    htpy-hom-Directed-Graph H G f
      ( comp-hom-Directed-Graph H
        ( Σ-Directed-Graph (fiber-hom-Directed-Graph H G f))
        ( G)
        ( pr1-Σ-Directed-Graph (fiber-hom-Directed-Graph H G f))
        ( hom-compute-Σ-fiber-hom-Directed-Graph H G f))
  htpy-compute-Σ-fiber-hom-Directed-Graph =
    refl-htpy-hom-Directed-Graph H G f
```

### The fibers of the first projection of a dependent sums of directed graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  fiber-pr1-Σ-Directed-Graph : Dependent-Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  fiber-pr1-Σ-Directed-Graph =
    fiber-hom-Directed-Graph
      ( Σ-Directed-Graph H)
      ( G)
      ( pr1-Σ-Directed-Graph H)

  vertex-fiber-pr1-Σ-Directed-Graph :
    (x : vertex-Directed-Graph G) → UU (l1 ⊔ l3)
  vertex-fiber-pr1-Σ-Directed-Graph =
    vertex-Dependent-Directed-Graph fiber-pr1-Σ-Directed-Graph

  edge-fiber-pr1-Σ-Directed-Graph :
    {x x' : vertex-Directed-Graph G} →
    edge-Directed-Graph G x x' →
    vertex-fiber-pr1-Σ-Directed-Graph x →
    vertex-fiber-pr1-Σ-Directed-Graph x' → UU (l2 ⊔ l4)
  edge-fiber-pr1-Σ-Directed-Graph =
    edge-Dependent-Directed-Graph fiber-pr1-Σ-Directed-Graph

  vertex-equiv-compute-fiber-pr1-Σ-Directed-Graph :
    fam-equiv
      ( vertex-fiber-pr1-Σ-Directed-Graph)
      ( vertex-Dependent-Directed-Graph H)
  vertex-equiv-compute-fiber-pr1-Σ-Directed-Graph =
    equiv-fiber-pr1 _

  vertex-compute-fiber-pr1-Σ-Directed-Graph :
    {x : vertex-Directed-Graph G} →
    vertex-fiber-pr1-Σ-Directed-Graph x →
    vertex-Dependent-Directed-Graph H x
  vertex-compute-fiber-pr1-Σ-Directed-Graph =
    map-fiber-pr1 _ _

  edge-equiv-compute-fiber-pr1-Σ-Directed-Graph :
    {x x' : vertex-Directed-Graph G}
    (a : edge-Directed-Graph G x x') →
    (y : vertex-fiber-pr1-Σ-Directed-Graph x) →
    (y' : vertex-fiber-pr1-Σ-Directed-Graph x') →
    edge-fiber-pr1-Σ-Directed-Graph a y y' ≃
    edge-Dependent-Directed-Graph H a
      ( vertex-compute-fiber-pr1-Σ-Directed-Graph y)
      ( vertex-compute-fiber-pr1-Σ-Directed-Graph y')
  edge-equiv-compute-fiber-pr1-Σ-Directed-Graph a (y , refl) (y' , refl) =
    equiv-fiber-pr1 _ _

  edge-compute-fiber-pr1-Σ-Directed-Graph :
    {x x' : vertex-Directed-Graph G}
    {a : edge-Directed-Graph G x x'} →
    {y : vertex-fiber-pr1-Σ-Directed-Graph x} →
    {y' : vertex-fiber-pr1-Σ-Directed-Graph x'} →
    edge-fiber-pr1-Σ-Directed-Graph a y y' →
    edge-Dependent-Directed-Graph H a
      ( vertex-compute-fiber-pr1-Σ-Directed-Graph y)
      ( vertex-compute-fiber-pr1-Σ-Directed-Graph y')
  edge-compute-fiber-pr1-Σ-Directed-Graph =
    map-equiv (edge-equiv-compute-fiber-pr1-Σ-Directed-Graph _ _ _)

  compute-fiber-pr1-Σ-Directed-Graph :
    equiv-Dependent-Directed-Graph fiber-pr1-Σ-Directed-Graph H
  pr1 compute-fiber-pr1-Σ-Directed-Graph =
    vertex-equiv-compute-fiber-pr1-Σ-Directed-Graph
  pr2 compute-fiber-pr1-Σ-Directed-Graph _ _ =
    edge-equiv-compute-fiber-pr1-Σ-Directed-Graph
```
