# Terminal reflexive graphs

```agda
module graph-theory.terminal-reflexive-graphs where
```

<details><summary>Idea</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.reflexive-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.terminal-directed-graphs
```

</details>

## Idea

The
{{#concept "terminal reflexive graph" Agda=is-terminal-Reflexive-Graph Agda=terminal-Reflexive-Graph}}
is a [reflexive graph](graph-theory.reflexive-graphs.md) `1` such that the type
of [graph homomorphisms](graph-theory.morphisms-reflexive-graphs.md) `hom A 1`
is [contractible](foundation-core.contractible-types.md) for any reflexive graph
`A`.

Concretely, the terminal reflexive graph `1` is defined by

```text
  1₀ := 1
  1₁ x y := 1.
```

## Definitions

### The predicate of being a terminal reflexive graph

The (small) predicate of being a terminal reflexive graph asserts that the type
of vertices and all types of edges are contractible.

```agda
module _
  {l1 l2 : Level} (A : Reflexive-Graph l1 l2)
  where

  is-terminal-prop-Reflexive-Graph : Prop (l1 ⊔ l2)
  is-terminal-prop-Reflexive-Graph =
    product-Prop
      ( is-contr-Prop (vertex-Reflexive-Graph A))
      ( Π-Prop
        ( vertex-Reflexive-Graph A)
        ( λ x →
          Π-Prop
            ( vertex-Reflexive-Graph A)
            ( λ y → is-contr-Prop (edge-Reflexive-Graph A x y))))

  is-terminal-Reflexive-Graph : UU (l1 ⊔ l2)
  is-terminal-Reflexive-Graph = type-Prop is-terminal-prop-Reflexive-Graph

  is-prop-is-terminal-Reflexive-Graph :
    is-prop is-terminal-Reflexive-Graph
  is-prop-is-terminal-Reflexive-Graph =
    is-prop-type-Prop is-terminal-prop-Reflexive-Graph
```

### The universal property of being a terminal reflexive graph

```agda
module _
  {l1 l2 : Level} (A : Reflexive-Graph l1 l2)
  where

  universal-property-terminal-Reflexive-Graph : UUω
  universal-property-terminal-Reflexive-Graph =
    {l3 l4 : Level} (X : Reflexive-Graph l3 l4) →
    is-contr (hom-Reflexive-Graph X A)
```

### The terminal reflexive graph

```agda
directed-graph-terminal-Reflexive-Graph : Directed-Graph lzero lzero
directed-graph-terminal-Reflexive-Graph = terminal-Directed-Graph

vertex-terminal-Reflexive-Graph : UU lzero
vertex-terminal-Reflexive-Graph =
  vertex-Directed-Graph directed-graph-terminal-Reflexive-Graph

edge-terminal-Reflexive-Graph :
  (x y : vertex-terminal-Reflexive-Graph) → UU lzero
edge-terminal-Reflexive-Graph =
  edge-Directed-Graph directed-graph-terminal-Reflexive-Graph

terminal-Reflexive-Graph : Reflexive-Graph lzero lzero
pr1 terminal-Reflexive-Graph = terminal-Directed-Graph
pr2 terminal-Reflexive-Graph _ = star
```
