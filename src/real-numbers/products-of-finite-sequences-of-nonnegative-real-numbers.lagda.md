# Products of finite sequences of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.products-of-finite-sequences-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.products-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence of nonnegative real numbers" Agda=product-fin-sequence-ℝ⁰⁺}}
extends the
[multiplication](real-numbers.multiplication-nonnegative-real-numbers.md)
operation on [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of nonnegative real numbers.

## Definition

```agda
real-product-fin-sequence-ℝ⁰⁺ :
  {l : Level} (n : ℕ) → fin-sequence (ℝ⁰⁺ l) n → ℝ l
real-product-fin-sequence-ℝ⁰⁺ n a =
  product-fin-sequence-ℝ n (real-ℝ⁰⁺ ∘ a)

abstract
  is-nonnegative-real-product-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l) n) →
    is-nonnegative-ℝ (real-product-fin-sequence-ℝ⁰⁺ n a)
  is-nonnegative-real-product-fin-sequence-ℝ⁰⁺ {l} 0 _ =
    ind-Σ (preserves-is-nonnegative-raise-ℝ l) one-ℝ⁰⁺
  is-nonnegative-real-product-fin-sequence-ℝ⁰⁺ (succ-ℕ n) a =
    is-nonnegative-mul-ℝ
      ( is-nonnegative-real-product-fin-sequence-ℝ⁰⁺ n (a ∘ inl-Fin n))
      ( is-nonnegative-real-ℝ⁰⁺ (a (neg-one-Fin n)))

product-fin-sequence-ℝ⁰⁺ :
  {l : Level} (n : ℕ) → fin-sequence (ℝ⁰⁺ l) n → ℝ⁰⁺ l
product-fin-sequence-ℝ⁰⁺ n a =
  ( real-product-fin-sequence-ℝ⁰⁺ n a ,
    is-nonnegative-real-product-fin-sequence-ℝ⁰⁺ n a)
```
