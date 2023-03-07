# Baire space

```agda
module set-theory.baire-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The Baire space is the type of functions `ℕ → ℕ`.

## Definition

```agda
baire-space : UU lzero
baire-space = ℕ → ℕ
```
