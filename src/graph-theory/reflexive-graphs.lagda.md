# Reflexive graphs

```agda
module graph-theory.reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
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
  Σ (UU l1) (λ V → Σ (V → V → UU l2) (λ E → (v : V) → E v v))

module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  vertex-Reflexive-Graph : UU l1
  vertex-Reflexive-Graph = pr1 G

  edge-Reflexive-Graph : vertex-Reflexive-Graph → vertex-Reflexive-Graph → UU l2
  edge-Reflexive-Graph = pr1 (pr2 G)

  refl-Reflexive-Graph : (x : vertex-Reflexive-Graph) → edge-Reflexive-Graph x x
  refl-Reflexive-Graph = pr2 (pr2 G)

  graph-Reflexive-Graph : Directed-Graph l1 l2
  graph-Reflexive-Graph = vertex-Reflexive-Graph , edge-Reflexive-Graph
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
