# The maybe monad on finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.maybe
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation-core.maybe public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
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
