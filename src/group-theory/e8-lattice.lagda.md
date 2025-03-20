# The `E₈`-lattice

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.e8-lattice
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-integers funext
open import elementary-number-theory.integers

open import foundation.equality-coproduct-types funext
open import foundation.sets funext
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Definition

### The ambient set of the E₈ lattice

The E₈ lattice itself is a subset of the following set.

```agda
ambient-set-E8-lattice : Set lzero
ambient-set-E8-lattice =
  coproduct-Set (hom-set-Set (Fin-Set 8) ℤ-Set) (hom-set-Set (Fin-Set 8) ℤ-Set)
```
