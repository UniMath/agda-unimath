# Terminal directed graphs

```agda
module graph-theory.terminal-directed-graphs where
```

<details><summary>Idea</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

The
{{#concept "terminal directed graph" Agda=is-terminal-Directed-Graph Agda=terminal-Directed-Graph}}
is a [directed graph](graph-theory.directed-graphs.md) `1` such that the type of
[graph homomorphisms](graph-theory.morphisms-directed-graphs.md) `hom A 1` is
[contractible](foundation-core.contractible-types.md) for any directed graph
`A`.

Concretely, the terminal directed graph `1` is defined by

```text
  1₀ := 1
  1₁ x y := 1.
```

## Definitions

### The predicate of being a terminal directed graph

The (small) predicate of being a terminal directed graph asserts that the type
of vertices and all types of edges are contractible.

```agda
module _
  {l1 l2 : Level} (A : Directed-Graph l1 l2)
  where

  is-terminal-prop-Directed-Graph : Prop (l1 ⊔ l2)
  is-terminal-prop-Directed-Graph =
    product-Prop
      ( is-contr-Prop (vertex-Directed-Graph A))
      ( Π-Prop
        ( vertex-Directed-Graph A)
        ( λ x →
          Π-Prop
            ( vertex-Directed-Graph A)
            ( λ y → is-contr-Prop (edge-Directed-Graph A x y))))

  is-terminal-Directed-Graph : UU (l1 ⊔ l2)
  is-terminal-Directed-Graph = type-Prop is-terminal-prop-Directed-Graph

  is-prop-is-terminal-Directed-Graph :
    is-prop is-terminal-Directed-Graph
  is-prop-is-terminal-Directed-Graph =
    is-prop-type-Prop is-terminal-prop-Directed-Graph
```

### The universal property of being a terminal directed graph

```agda
module _
  {l1 l2 : Level} (A : Directed-Graph l1 l2)
  where

  universal-property-terminal-Directed-Graph : UUω
  universal-property-terminal-Directed-Graph =
    {l3 l4 : Level} (X : Directed-Graph l3 l4) →
    is-contr (hom-Directed-Graph X A)
```

### The terminal directed graph

```agda
vertex-terminal-Directed-Graph : UU lzero
vertex-terminal-Directed-Graph = unit

edge-terminal-Directed-Graph :
  (x y : vertex-terminal-Directed-Graph) → UU lzero
edge-terminal-Directed-Graph x y = unit

terminal-Directed-Graph : Directed-Graph lzero lzero
pr1 terminal-Directed-Graph = vertex-terminal-Directed-Graph
pr2 terminal-Directed-Graph = edge-terminal-Directed-Graph
```
