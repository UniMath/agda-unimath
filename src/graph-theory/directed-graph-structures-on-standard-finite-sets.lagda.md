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
