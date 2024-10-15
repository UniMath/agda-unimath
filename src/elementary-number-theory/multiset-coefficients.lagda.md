# Multiset coefficients

```agda
module elementary-number-theory.multiset-coefficients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The multiset coefficients count the number of [multisets](trees.multisets.md) of
size `k` of elements of a [set](foundation-core.sets.md) of size `n`. In other
words, it counts the number of
[connected componets](foundation.connected-components.md) of the type

```text
  Σ (A : Fin n → 𝔽), ║ Fin k ≃ Σ (i : Fin n), A i ║.
```

The first few numbers are

|  n\k  |   0 |   1 |   2 |   3 |   4 |   5 |
| :---: | --: | --: | --: | --: | --: | --: |
| **0** |   1 |   0 |   0 |   0 |   0 |   0 |
| **1** |   1 |   1 |   1 |   1 |   1 |   1 |
| **2** |   1 |   2 |   3 |   4 |   5 |   6 |
| **3** |   1 |   3 |   6 |  10 |  15 |  21 |
| **4** |   1 |   4 |  10 |  20 |  35 |  56 |
| **5** |   1 |   5 |  15 |  35 |  70 | 126 |

## Definition

```agda
multiset-coefficient : ℕ → ℕ → ℕ
multiset-coefficient zero-ℕ zero-ℕ = 1
multiset-coefficient zero-ℕ (succ-ℕ k) = 0
multiset-coefficient (succ-ℕ n) zero-ℕ = 1
multiset-coefficient (succ-ℕ n) (succ-ℕ k) =
  (multiset-coefficient (succ-ℕ n) k) +ℕ (multiset-coefficient n (succ-ℕ k))
```
