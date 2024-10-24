# Discrete graphs

```agda
module graph-theory.discrete-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.discrete-relations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import graph-theory.directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A [directed graph](graph-theory.directed-graphs.md) `G ≐ (V , E)` is said to be
{{#concept "discrete" Disambiguation="graph" Agda=is-discrete-Graph}} if, for
every vertex `x : V`, the type family of edges with source `x`, `E x`, is
[torsorial](foundation-core.torsorial-type-families.md). In other words, if the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : V), (E x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`. The
{{#concept "standard discrete graph"}} associated to a type `X` is the graph
whose vertices are elements of `X`, and edges are
[identifications](foundation-core.identity-types.md),

```text
  E x y := (x ＝ y).
```

## Definitions

### The predicate on graphs of being discrete

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-discrete-prop-Graph : Prop (l1 ⊔ l2)
  is-discrete-prop-Graph = is-discrete-prop-Relation (edge-Directed-Graph G)

  is-discrete-Graph : UU (l1 ⊔ l2)
  is-discrete-Graph = type-Prop is-discrete-prop-Graph

  is-prop-is-discrete-Graph : is-prop is-discrete-Graph
  is-prop-is-discrete-Graph = is-prop-type-Prop is-discrete-prop-Graph
```

### The predicate on reflexive graphs of being discrete

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  is-discrete-prop-Reflexive-Graph : Prop (l1 ⊔ l2)
  is-discrete-prop-Reflexive-Graph =
    is-discrete-prop-Graph (directed-graph-Reflexive-Graph G)

  is-discrete-Reflexive-Graph : UU (l1 ⊔ l2)
  is-discrete-Reflexive-Graph =
    type-Prop is-discrete-prop-Reflexive-Graph

  is-prop-is-discrete-Reflexive-Graph : is-prop is-discrete-Reflexive-Graph
  is-prop-is-discrete-Reflexive-Graph =
    is-prop-type-Prop is-discrete-prop-Reflexive-Graph
```
