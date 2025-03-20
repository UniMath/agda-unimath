# Steiner triple systems

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.steiner-triple-systems
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.steiner-systems funext
```

</details>

## Definition

```agda
Steiner-Triple-System : ℕ → UU (lsuc lzero)
Steiner-Triple-System n = Steiner-System 2 3 n
```
