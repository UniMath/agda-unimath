# Equivalences of enriched undirected graphs

```agda
module graph-theory.equivalences-enriched-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.enriched-undirected-graphs
open import graph-theory.equivalences-undirected-graphs
open import graph-theory.neighbors-undirected-graphs
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of enriched undirected graphs" Agda=equiv-Enriched-Undirected-Graph}}
of
`(A,B)`-[enriched undirected graphs](graph-theory.enriched-undirected-graphs.md)
from `G` to `H` consists of an
[equivalence](graph-theory.equivalences-undirected-graphs.md) `e` of the
underlying [graphs](graph-theory.undirected-graphs.md) of `G` and `H` such that
preserving the labeling and the [equivalences](foundation-core.equivalences.md)
on the [neighbors](graph-theory.neighbors-undirected-graphs.md).

## Definition

### Equivalences between enriched undirected graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  (H : Enriched-Undirected-Graph l5 l6 A B)
  where

  equiv-Enriched-Undirected-Graph :
    UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-Enriched-Undirected-Graph =
    Σ ( equiv-Undirected-Graph
        ( undirected-graph-Enriched-Undirected-Graph A B G)
        ( undirected-graph-Enriched-Undirected-Graph A B H))
      ( λ e →
        Σ ( ( shape-vertex-Enriched-Undirected-Graph A B G) ~
            ( ( shape-vertex-Enriched-Undirected-Graph A B H) ∘
              ( vertex-equiv-Undirected-Graph
                ( undirected-graph-Enriched-Undirected-Graph A B G)
                ( undirected-graph-Enriched-Undirected-Graph A B H)
                ( e))))
          ( λ α →
            ( x : vertex-Enriched-Undirected-Graph A B G) →
            htpy-equiv
              ( ( equiv-neighbor-equiv-Undirected-Graph
                  ( undirected-graph-Enriched-Undirected-Graph A B G)
                  ( undirected-graph-Enriched-Undirected-Graph A B H)
                  ( e)
                  ( x)) ∘e
                ( equiv-neighbor-Enriched-Undirected-Graph A B G x))
              ( ( equiv-neighbor-Enriched-Undirected-Graph A B H
                  ( vertex-equiv-Undirected-Graph
                    ( undirected-graph-Enriched-Undirected-Graph A B G)
                    ( undirected-graph-Enriched-Undirected-Graph A B H)
                    ( e)
                    ( x))) ∘e
                ( equiv-tr B (α x)))))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  (H : Enriched-Undirected-Graph l5 l6 A B)
  (e : equiv-Enriched-Undirected-Graph A B G H)
  where

  equiv-undirected-graph-equiv-Enriched-Undirected-Graph :
    equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
  equiv-undirected-graph-equiv-Enriched-Undirected-Graph = pr1 e

  vertex-equiv-equiv-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph A B G ≃
    vertex-Enriched-Undirected-Graph A B H
  vertex-equiv-equiv-Enriched-Undirected-Graph =
    vertex-equiv-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  vertex-equiv-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph A B G →
    vertex-Enriched-Undirected-Graph A B H
  vertex-equiv-Enriched-Undirected-Graph =
    vertex-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  equiv-unordered-pair-vertices-equiv-Enriched-Undirected-Graph :
    unordered-pair-vertices-Enriched-Undirected-Graph A B G ≃
    unordered-pair-vertices-Enriched-Undirected-Graph A B H
  equiv-unordered-pair-vertices-equiv-Enriched-Undirected-Graph =
    equiv-unordered-pair-vertices-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  unordered-pair-vertices-equiv-Enriched-Undirected-Graph :
    unordered-pair-vertices-Enriched-Undirected-Graph A B G →
    unordered-pair-vertices-Enriched-Undirected-Graph A B H
  unordered-pair-vertices-equiv-Enriched-Undirected-Graph =
    unordered-pair-vertices-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  edge-equiv-equiv-Enriched-Undirected-Graph :
    ( p : unordered-pair-vertices-Enriched-Undirected-Graph A B G) →
    edge-Enriched-Undirected-Graph A B G p ≃
    edge-Enriched-Undirected-Graph A B H
      ( unordered-pair-vertices-equiv-Enriched-Undirected-Graph p)
  edge-equiv-equiv-Enriched-Undirected-Graph =
    edge-equiv-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  edge-equiv-Enriched-Undirected-Graph :
    ( p : unordered-pair-vertices-Enriched-Undirected-Graph A B G) →
    edge-Enriched-Undirected-Graph A B G p →
    edge-Enriched-Undirected-Graph A B H
      ( unordered-pair-vertices-equiv-Enriched-Undirected-Graph p)
  edge-equiv-Enriched-Undirected-Graph =
    edge-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
      ( equiv-undirected-graph-equiv-Enriched-Undirected-Graph)

  shape-equiv-Enriched-Undirected-Graph :
    (v : vertex-Enriched-Undirected-Graph A B G) →
    ( shape-vertex-Enriched-Undirected-Graph A B G v) ＝
    ( shape-vertex-Enriched-Undirected-Graph A B H
      ( vertex-equiv-Enriched-Undirected-Graph v))
  shape-equiv-Enriched-Undirected-Graph = pr1 (pr2 e)
```

### The identity equivalence of an enriched undirected graph

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  where

  id-equiv-Enriched-Undirected-Graph :
    equiv-Enriched-Undirected-Graph A B G G
  pr1 id-equiv-Enriched-Undirected-Graph =
    id-equiv-Undirected-Graph (undirected-graph-Enriched-Undirected-Graph A B G)
  pr1 (pr2 id-equiv-Enriched-Undirected-Graph) = refl-htpy
  pr2 (pr2 id-equiv-Enriched-Undirected-Graph) x b =
    neighbor-id-equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( x)
      ( map-equiv-neighbor-Enriched-Undirected-Graph A B G x b)
```

## Properties

### Univalence for enriched undirected graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  where

  is-torsorial-equiv-Enriched-Undirected-Graph :
    is-torsorial (equiv-Enriched-Undirected-Graph A B G)
  is-torsorial-equiv-Enriched-Undirected-Graph =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Undirected-Graph
        ( undirected-graph-Enriched-Undirected-Graph A B G))
      ( pair
        ( undirected-graph-Enriched-Undirected-Graph A B G)
        ( id-equiv-Undirected-Graph
          ( undirected-graph-Enriched-Undirected-Graph A B G)))
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy
          ( shape-vertex-Enriched-Undirected-Graph A B G))
        ( pair
          ( shape-vertex-Enriched-Undirected-Graph A B G)
          ( refl-htpy))
        ( is-torsorial-Eq-Π
          ( λ x →
            is-torsorial-htpy-equiv
              ( equiv-neighbor-equiv-Undirected-Graph
                  ( undirected-graph-Enriched-Undirected-Graph A B G)
                  ( undirected-graph-Enriched-Undirected-Graph A B G)
                  ( id-equiv-Undirected-Graph
                    ( undirected-graph-Enriched-Undirected-Graph A B G))
                  ( x) ∘e
                ( equiv-neighbor-Enriched-Undirected-Graph A B G x)))))

  equiv-eq-Enriched-Undirected-Graph :
    (H : Enriched-Undirected-Graph l3 l4 A B) →
    (G ＝ H) → equiv-Enriched-Undirected-Graph A B G H
  equiv-eq-Enriched-Undirected-Graph H refl =
    id-equiv-Enriched-Undirected-Graph A B G

  is-equiv-equiv-eq-Enriched-Undirected-Graph :
    (H : Enriched-Undirected-Graph l3 l4 A B) →
    is-equiv (equiv-eq-Enriched-Undirected-Graph H)
  is-equiv-equiv-eq-Enriched-Undirected-Graph =
    fundamental-theorem-id
      ( is-torsorial-equiv-Enriched-Undirected-Graph)
      ( equiv-eq-Enriched-Undirected-Graph)

  extensionality-Enriched-Undirected-Graph :
    (H : Enriched-Undirected-Graph l3 l4 A B) →
    (G ＝ H) ≃ equiv-Enriched-Undirected-Graph A B G H
  pr1 (extensionality-Enriched-Undirected-Graph H) =
    equiv-eq-Enriched-Undirected-Graph H
  pr2 (extensionality-Enriched-Undirected-Graph H) =
    is-equiv-equiv-eq-Enriched-Undirected-Graph H

  eq-equiv-Enriched-Undirected-Graph :
    (H : Enriched-Undirected-Graph l3 l4 A B) →
    equiv-Enriched-Undirected-Graph A B G H → (G ＝ H)
  eq-equiv-Enriched-Undirected-Graph H =
    map-inv-equiv (extensionality-Enriched-Undirected-Graph H)
```

## External links

- [Graph isomoprhism](https://www.wikidata.org/entity/Q303100) at Wikidata
- [Graph isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphism) at
  Wikipedia
- [Graph isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.html) at
  Wolfram MathWorld
- [Isomorphism](https://ncatlab.org/nlab/show/isomorphism) at $n$Lab
