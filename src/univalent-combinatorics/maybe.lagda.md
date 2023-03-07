# The maybe modality on finite types

```agda
module univalent-combinatorics.maybe where
```

<details><summary>Imports</summary>
```agda
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import foundation.maybe public
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
```
</details>

```agda
add-free-point-UU-Fin :
  {l1 : Level} (k : ℕ) → UU-Fin l1 k → UU-Fin l1 (succ-ℕ k)
add-free-point-UU-Fin k X = coprod-UU-Fin k 1 X unit-UU-Fin
```
