# Steiner triple systems

```agda
module univalent-combinatorics.steiner-triple-systems where
```

<details><summary>Imports</summary>
```agda
open import univalent-combinatorics.steiner-systems
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
```
</details>

## Definition

```agda
Steiner-Triple-System : ℕ → UU (lsuc lzero)
Steiner-Triple-System n = Steiner-System 2 3 n
```

