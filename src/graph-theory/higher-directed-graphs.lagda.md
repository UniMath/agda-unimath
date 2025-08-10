# Higher directed graphs

```agda
module graph-theory.higher-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Idea

A {{#concept "directed `n`-graph" Agda=Higher-Directed-Graph}} consists of a
type of vertices equipped with a binary family of directed `n-1`-graphs on its
edges, where a directed `0`-graph consists of just a type of vertices.

## Definition

### The structure of a higher directed graph on a type of vertices

```agda
is-higher-directed-graph-succ :
  {l1 : Level} (l2 : Level) (n : ℕ) → UU l1 → UU (l1 ⊔ lsuc l2)
is-higher-directed-graph-succ l2 zero-ℕ V =
  Relation l2 V
is-higher-directed-graph-succ l2 (succ-ℕ n) V =
  Σ ( is-higher-directed-graph-succ l2 0 V)
    ( λ E → (u v : V) → is-higher-directed-graph-succ l2 n (E u v))

edge-is-higher-directed-graph-succ :
  {l1 l2 : Level} {n : ℕ} (V : UU l1) →
  is-higher-directed-graph-succ l2 n V → Relation l2 V
edge-is-higher-directed-graph-succ {n = zero-ℕ} V E = E
edge-is-higher-directed-graph-succ {n = succ-ℕ n} V (E , _) = E
```

### The type of higher directed graphs

```agda
Higher-Directed-Graph : (l : Level) (n : ℕ) → UU (lsuc l)
Higher-Directed-Graph l 0 = UU l
Higher-Directed-Graph l (succ-ℕ n) =
  Σ (UU l) (λ V → V → V → Higher-Directed-Graph l n)

vertex-Higher-Directed-Graph :
  {n : ℕ} {l : Level} → Higher-Directed-Graph l n → UU l
vertex-Higher-Directed-Graph {0} G = G
vertex-Higher-Directed-Graph {succ-ℕ n} = pr1

edge-Higher-Directed-Graph :
  {n : ℕ} {l : Level} (G : Higher-Directed-Graph l (succ-ℕ n)) →
  vertex-Higher-Directed-Graph G → vertex-Higher-Directed-Graph G → UU l
edge-Higher-Directed-Graph {0} = pr2
edge-Higher-Directed-Graph {succ-ℕ n} G x y = pr1 (pr2 G x y)
```

## Properties

### Directed 1-graphs are just directed graphs

```agda
eq-Directed-Graph-Higher-Directed-Graph-1 :
  {l : Level} → Higher-Directed-Graph l 1 ＝ Directed-Graph l l
eq-Directed-Graph-Higher-Directed-Graph-1 = refl
```
