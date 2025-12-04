# Sums of finite sequences of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence of nonnegative real numbers" Agda=sum-fin-sequence-ℝ⁰⁺}}
extends the [addition](real-numbers.addition-nonnegative-real-numbers.md)
operation on [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of real numbers.

## Definition

```agda
real-sum-fin-sequence-ℝ⁰⁺ : {l : Level} (n : ℕ) → fin-sequence (ℝ⁰⁺ l) n → ℝ l
real-sum-fin-sequence-ℝ⁰⁺ n a =
  sum-fin-sequence-ℝ n (real-ℝ⁰⁺ ∘ a)

abstract
  is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l) n) →
    is-nonnegative-ℝ (real-sum-fin-sequence-ℝ⁰⁺ n a)
  is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ {l} 0 _ =
    ind-Σ (preserves-is-nonnegative-raise-ℝ l) zero-ℝ⁰⁺
  is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ (succ-ℕ n) a =
    is-nonnegative-real-add-ℝ⁰⁺
      ( real-sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl-Fin n) ,
        is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl-Fin n))
      ( a (neg-one-Fin n))

sum-fin-sequence-ℝ⁰⁺ : {l : Level} (n : ℕ) → fin-sequence (ℝ⁰⁺ l) n → ℝ⁰⁺ l
sum-fin-sequence-ℝ⁰⁺ n a =
  ( real-sum-fin-sequence-ℝ⁰⁺ n a ,
    is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ n a)
```
