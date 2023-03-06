# Baire space

<details><summary>Imports</summary>
```agda
module set-theory.baire-space where
open import elementary-number-theory.natural-numbers
open import foundation.universe-levels
```
</details>

## Idea

The Baire space is the type of functions `ℕ → ℕ`.

## Definition

```agda
baire-space : UU lzero
baire-space = ℕ → ℕ
```
