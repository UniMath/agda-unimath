# Undirected graph structures on standard finite sets

```agda
open import foundation.function-extensionality-axiom

module
  graph-theory.undirected-graph-structures-on-standard-finite-sets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-pairs funext

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Definition

```agda
Undirected-Graph-Fin : UU (lsuc lzero)
Undirected-Graph-Fin = Σ ℕ (λ V → unordered-pair (Fin V) → ℕ)
```

## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Graph](https://mathworld.wolfram.com/Graph.html) at Wolfram MathWorld
