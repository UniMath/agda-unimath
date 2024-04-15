# The maybe modality on finite types

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
add-free-point-UU-Fin :
  {l1 : Level} (k : ℕ) → UU-Fin l1 k → UU-Fin l1 (succ-ℕ k)
add-free-point-UU-Fin k X = coproduct-UU-Fin k 1 X unit-UU-Fin
```
