# Standard finite pruned trees

```agda
module univalent-combinatorics.standard-finite-pruned-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A standard finite pruned tree of height `n` can be thought of as a standard
finite tree in which each path from the root to a leaf has length `n + 1`.

## Definition

```agda
data Pruned-Tree-Fin : ℕ → UU lzero where
  root-Pruned-Tree-Fin : Pruned-Tree-Fin zero-ℕ
  tree-Pruned-Tree-Fin :
    (n k : ℕ) → (Fin k → Pruned-Tree-Fin n) → Pruned-Tree-Fin (succ-ℕ n)

width-Pruned-Tree-Fin : (n : ℕ) → Pruned-Tree-Fin (succ-ℕ n) → ℕ
width-Pruned-Tree-Fin n (tree-Pruned-Tree-Fin .n k x) = k
```
