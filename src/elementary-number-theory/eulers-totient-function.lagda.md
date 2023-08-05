# Euler's totient function

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module elementary-number-theory.eulers-totient-function where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Euler's totient function** `φ : ℕ → ℕ` is the function that maps a natural
number `n` to the number of `x < n` that are relatively prime with `n`.

## Definition

```agda
eulers-totient-function : ℕ → ℕ
eulers-totient-function n =
  number-of-elements-subset-𝔽
    ( Fin-𝔽 n)
    ( λ x → is-relatively-prime-ℕ-Decidable-Prop (nat-Fin n x) n)
```
