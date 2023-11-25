# Complete bipartite graphs

```agda
module graph-theory.complete-bipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
```

</details>

## Definition

```agda
complete-bipartite-Undirected-Graph-𝔽 :
  {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → Undirected-Graph-𝔽 (l1 ⊔ l2) (l1 ⊔ l2)
pr1 (complete-bipartite-Undirected-Graph-𝔽 X Y) = coprod-𝔽 X Y
pr2 (complete-bipartite-Undirected-Graph-𝔽 X Y) p =
  prod-𝔽
    ( Σ-𝔽 X
      ( λ x →
        fiber-𝔽
          ( finite-type-2-Element-Type (pr1 p))
          ( coprod-𝔽 X Y)
          ( element-unordered-pair p)
          ( inl x)))
    ( Σ-𝔽 Y
      ( λ y →
        fiber-𝔽
          ( finite-type-2-Element-Type (pr1 p))
          ( coprod-𝔽 X Y)
          ( element-unordered-pair p)
          ( inr y)))
```

## External links

- [Complete bipartite graph](https://d3gt.com/unit.html?complete-bipartite) at
  D3 Graph Theory
- [Bipartite graphs](https://ncatlab.org/nlab/show/bipartite+graph) at $n$Lab
- [Complete bipartite graph](https://www.wikidata.org/entity/Q913598) at
  Wikidata
- [Complete bipartite graph](https://en.wikipedia.org/wiki/Complete_bipartite_graph)
  at Wikipedia
- [Complete bipartite graphs](https://mathworld.wolfram.com/CompleteBipartiteGraph.html)
  at Wolfram Mathworld
