# Reflexive graphs

```agda
module graph-theory.reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-dependent-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.reflexive-relations
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Idea

A {{#concept "reflexive graph" Agda=Reflexive-Graph}} is a
[directed graph](graph-theory.directed-graphs.md)
[equipped](foundation.structure.md) with a loop edge at every vertex.

## Definition

```agda
Reflexive-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Reflexive-Graph l1 l2 =
  Σ ( Directed-Graph l1 l2)
    ( λ G → (x : vertex-Directed-Graph G) → edge-Directed-Graph G x x)

module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  directed-graph-Reflexive-Graph : Directed-Graph l1 l2
  directed-graph-Reflexive-Graph = pr1 G

  vertex-Reflexive-Graph : UU l1
  vertex-Reflexive-Graph = vertex-Directed-Graph directed-graph-Reflexive-Graph

  edge-Reflexive-Graph : vertex-Reflexive-Graph → vertex-Reflexive-Graph → UU l2
  edge-Reflexive-Graph = edge-Directed-Graph directed-graph-Reflexive-Graph

  refl-Reflexive-Graph : (x : vertex-Reflexive-Graph) → edge-Reflexive-Graph x x
  refl-Reflexive-Graph = pr2 G

  reflexive-relation-Reflexive-Graph :
    Reflexive-Relation l2 vertex-Reflexive-Graph
  pr1 reflexive-relation-Reflexive-Graph = edge-Reflexive-Graph
  pr2 reflexive-relation-Reflexive-Graph = refl-Reflexive-Graph

  binary-dependent-identification-refl-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph} (p : x ＝ y) →
    binary-dependent-identification edge-Reflexive-Graph p p
      ( refl-Reflexive-Graph x)
      ( refl-Reflexive-Graph y)
  binary-dependent-identification-refl-Reflexive-Graph =
    binary-dependent-identification-refl-Reflexive-Relation
      reflexive-relation-Reflexive-Graph
```

## See also

- [Large reflexive graphs](graph-theory.large-reflexive-graphs.md)
- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)

## External links

- [Reflexive graph](https://ncatlab.org/nlab/show/reflexive+graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Reflexive graph](https://mathworld.wolfram.com/ReflexiveGraph.html) at
  Wolfram MathWorld
