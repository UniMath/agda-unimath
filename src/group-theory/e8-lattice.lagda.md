#  The E₈-lattice

<details><summary>Imports</summary>
```agda
module group-theory.e8-lattice where

open import elementary-number-theory.integers

open import foundation.equality-coproduct-types
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```
</details>

## Definition

### The ambient set of the E₈ lattice

The E₈ lattice itself is a subset of the following set.

```agda
ambient-set-E8-lattice : Set lzero
ambient-set-E8-lattice =
  coprod-Set (hom-Set (Fin-Set 8) ℤ-Set) (hom-Set (Fin-Set 8) ℤ-Set)
```
