# Higher directed graphs

```agda
module graph-theory.higher-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Idea

A {{#concept "directed `n`-graph" Agda=Directed-Higher-Graph}} consists of a
type of vertices equipped with a binary family of directed `n-1`-graphs on its
edges, where a directed `0`-graph consists of just a type of vertices.

## Definition

```agda
Directed-Higher-Graph : (l : Level) (n : ℕ) → UU (lsuc l)
Directed-Higher-Graph l 0 = UU l
Directed-Higher-Graph l (succ-ℕ n) =
  Σ (UU l) (λ V → V → V → Directed-Higher-Graph l n)

vertex-Directed-Higher-Graph :
  {n : ℕ} {l : Level} → Directed-Higher-Graph l n → UU l
vertex-Directed-Higher-Graph {0} G = G
vertex-Directed-Higher-Graph {succ-ℕ n} = pr1

edge-Directed-Higher-Graph :
  {n : ℕ} {l : Level} (G : Directed-Higher-Graph l (succ-ℕ n)) →
  vertex-Directed-Higher-Graph G → vertex-Directed-Higher-Graph G → UU l
edge-Directed-Higher-Graph {0} = pr2
edge-Directed-Higher-Graph {succ-ℕ n} G x y = pr1 (pr2 G x y)
```

## Properties

### Directed 1-graphs are just directed graphs

```agda
eq-Directed-Graph-Directed-Higher-Graph-1 :
  {l : Level} → Directed-Higher-Graph l 1 ＝ Directed-Graph l l
eq-Directed-Graph-Directed-Higher-Graph-1 = refl
```
