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
add-free-point-Type-With-Finite-Cardinality :
  {l1 : Level} (k : ℕ) → Type-With-Finite-Cardinality l1 k → Type-With-Finite-Cardinality l1 (succ-ℕ k)
add-free-point-Type-With-Finite-Cardinality k X = coproduct-Type-With-Finite-Cardinality k 1 X unit-Type-With-Finite-Cardinality
```
