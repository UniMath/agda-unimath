# Steiner triple systems

```agda
module univalent-combinatorics.steiner-triple-systems where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.steiner-systems
```

</details>

## Definition

```agda
Steiner-Triple-System : ℕ → UU lone
Steiner-Triple-System n = Steiner-System 2 3 n
```
