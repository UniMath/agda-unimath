# Undirected graph structures on standard finite sets

```agda
module graph-theory.undirected-graph-structures-on-standard-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

```agda
Undirected-Graph-Fin : UU (lsuc lzero)
Undirected-Graph-Fin = Σ ℕ (λ V → unordered-pair (Fin V) → ℕ)
```
