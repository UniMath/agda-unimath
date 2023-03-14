# Cantor space

```agda
module set-theory.cantor-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The Cantor space is the type of functions `ℕ → Fin 2`.

## Definition

```agda
cantor-space : UU lzero
cantor-space = ℕ → Fin 2
```

## Properties

### The cantor space has a tight apartness relation

```agda
cantor-space-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
cantor-space-Type-With-Tight-Apartness =
  exp-Type-With-Tight-Apartness ℕ (Fin-Type-With-Tight-Apartness 2)
```
