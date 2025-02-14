# The maybe monad on finite types

```agda
module univalent-combinatorics.maybe where

open import foundation.maybe public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
```

</details>

```agda
add-free-point-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ) →
  Type-With-Cardinality-ℕ l1 k →
  Type-With-Cardinality-ℕ l1 (succ-ℕ k)
add-free-point-Type-With-Cardinality-ℕ k X =
  coproduct-Type-With-Cardinality-ℕ k 1 X unit-Type-With-Cardinality-ℕ
```
