# Large higher directed graphs

```agda
module graph-theory.large-higher-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.higher-directed-graphs
```

</details>

## Idea

A {{#concept "large directed `n`-graph" Agda=Large-Higher-Directed-Graph}} is
defined inductively:

- A large directed $0$-graph is a large collection of vertices.
- A large directed $n+1$-graph is a large collection of vertices together with a
  [large binary relation](foundation.large-binary-relations.md) `E` on the
  vertices, such that `E u v` is a
  [(small) directed $n$-graph](graph-theory.higher-directed-graphs.md) for all
  `u` and `v`.

## Definitions

### The structure of a large higher directed graph on a large collection of vertices

```agda
data
  is-large-higher-directed-graph
  {α : Level → Level}
  (β γ : Level → Level → Level)
  (V : (l : Level) → UU (α l)) :
  (n : ℕ) → UUω
  where

  cons-zero-is-large-higher-directed-graph :
    is-large-higher-directed-graph β γ V 0

  cons-base-is-large-higher-directed-graph :
    Large-Relation β V → is-large-higher-directed-graph β γ V 1

  cons-ind-is-large-higher-directed-graph :
    (n : ℕ) →
    (E : Large-Relation β V) →
    ( {l1 l2 : Level} (u : V l1) (v : V l2) →
      is-higher-directed-graph-succ (γ l1 l2) n (E u v)) →
    is-large-higher-directed-graph β γ V (succ-ℕ (succ-ℕ n))

edge-is-large-higher-directed-graph :
  {α : Level → Level}
  (β γ : Level → Level → Level)
  (n : ℕ)
  (V : (l : Level) → UU (α l)) →
  is-large-higher-directed-graph β γ V (succ-ℕ n) →
  Large-Relation β V
edge-is-large-higher-directed-graph
  β γ .0 V (cons-base-is-large-higher-directed-graph E) =
  E
edge-is-large-higher-directed-graph
  β γ .(succ-ℕ n) V (cons-ind-is-large-higher-directed-graph n E _) =
  E
```

### The large type of large higher directed graphs

```agda
record
  Large-Higher-Directed-Graph
    (α : Level → Level) (β γ : Level → Level → Level) (n : ℕ) : UUω
  where

  field
    vertex-Large-Higher-Directed-Graph : (l : Level) → UU (α l)

    is-higher-directed-graph-Large-Higher-Directed-Graph :
      is-large-higher-directed-graph β γ vertex-Large-Higher-Directed-Graph n

open Large-Higher-Directed-Graph public

edge-Large-Higher-Directed-Graph :
  {α : Level → Level} {β γ : Level → Level → Level} {n : ℕ}
  (G : Large-Higher-Directed-Graph α β γ (succ-ℕ n)) →
  Large-Relation β (vertex-Large-Higher-Directed-Graph G)
edge-Large-Higher-Directed-Graph {α} {β} {γ} {n} G =
  edge-is-large-higher-directed-graph β γ n
    ( vertex-Large-Higher-Directed-Graph G)
    ( is-higher-directed-graph-Large-Higher-Directed-Graph G)
```
