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

A {{#concept "directed `n`-graph"}} consists of a type of vertices equipped with
a binary family of directed `n-1`-graphs on its edges, where a directed
`0`-graph consists of just a type of vertices.

## Definition

```agda
Directed-Higher-Graph : (n : ℕ) (l : Level) → UU (lsuc l)
Directed-Higher-Graph 0 l = UU l
Directed-Higher-Graph (succ-ℕ n) l = Σ (UU l) (λ V → V → V → UU l)

vertex-Directed-Higher-Graph :
  {n : ℕ} {l : Level} → Directed-Higher-Graph n l → UU l
vertex-Directed-Higher-Graph {0} G = G
vertex-Directed-Higher-Graph {succ-ℕ n} = pr1
```

## Properties

### Directed 1-graphs are just directed graphs

```agda
eq-Directed-Graph-Directed-Higher-Graph-1 :
  {l : Level} → Directed-Higher-Graph 1 l ＝ Directed-Graph l l
eq-Directed-Graph-Directed-Higher-Graph-1 = refl
```
