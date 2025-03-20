# Totally faithful morphisms of undirected graphs

```agda
open import foundation.function-extensionality-axiom

module
  graph-theory.totally-faithful-morphisms-undirected-graphs
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.universe-levels

open import graph-theory.morphisms-undirected-graphs funext
open import graph-theory.undirected-graphs funext
```

</details>

## Idea

A **totally faithful morphism of undirected graphs** is a
[morphism](graph-theory.morphisms-undirected-graphs.md) `f : G → H` of
[undirected graphs](graph-theory.undirected-graphs.md) such that for edge `e` in
`H` there is at most one edge in `G` that `f` maps to `e`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  is-totally-faithful-hom-Undirected-Graph :
    hom-Undirected-Graph G H → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l4)
  is-totally-faithful-hom-Undirected-Graph f =
    is-emb (tot (edge-hom-Undirected-Graph G H f))

  totally-faithful-hom-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  totally-faithful-hom-Undirected-Graph =
    Σ (hom-Undirected-Graph G H) is-totally-faithful-hom-Undirected-Graph

module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (f : totally-faithful-hom-Undirected-Graph G H)
  where

  hom-totally-faithful-hom-Undirected-Graph : hom-Undirected-Graph G H
  hom-totally-faithful-hom-Undirected-Graph = pr1 f

  vertex-totally-faithful-hom-Undirected-Graph :
    vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-totally-faithful-hom-Undirected-Graph =
    vertex-hom-Undirected-Graph G H hom-totally-faithful-hom-Undirected-Graph

  unordered-pair-vertices-totally-faithful-hom-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-totally-faithful-hom-Undirected-Graph =
    unordered-pair-vertices-hom-Undirected-Graph G H
      hom-totally-faithful-hom-Undirected-Graph

  edge-totally-faithful-hom-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-totally-faithful-hom-Undirected-Graph p)
  edge-totally-faithful-hom-Undirected-Graph =
    edge-hom-Undirected-Graph G H hom-totally-faithful-hom-Undirected-Graph

  is-totally-faithful-totally-faithful-hom-Undirected-Graph :
    is-totally-faithful-hom-Undirected-Graph G H
      hom-totally-faithful-hom-Undirected-Graph
  is-totally-faithful-totally-faithful-hom-Undirected-Graph = pr2 f
```

## See also

- [Embeddings of undirected graphs](graph-theory.embeddings-undirected-graphs.md)
- [Faithful morphisms of undirected graphs](graph-theory.faithful-morphisms-undirected-graphs.md)

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) at
  Wikipedia
