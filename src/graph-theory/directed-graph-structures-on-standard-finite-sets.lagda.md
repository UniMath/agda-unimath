# Directed graph structures on standard finite sets

```agda
module graph-theory.directed-graph-structures-on-standard-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

```agda
Directed-Graph-Fin : UU lzero
Directed-Graph-Fin = Σ ℕ (λ V → Fin V → Fin V → ℕ)
```

## External links

- [Digraph](https://ncatlab.org/nlab/show/digraph) at $n$Lab
- [Directed graph](https://ncatlab.org/nlab/show/directed+graph) at $n$Lab
- [Directed graph](https://www.wikidata.org/entity/Q1137726) on Wikdiata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Directed graph](https://mathworld.wolfram.com/DirectedGraph.html) at Wolfram
  Mathworld
