# Sums of finite sequences of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers where
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

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
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

## Properties

### Permutations preserve sums

```agda
abstract
  preserves-sum-permutation-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (σ : Permutation n) (a : fin-sequence (ℝ⁰⁺ l) n) →
    sum-fin-sequence-ℝ⁰⁺ n a ＝ sum-fin-sequence-ℝ⁰⁺ n (a ∘ map-equiv σ)
  preserves-sum-permutation-fin-sequence-ℝ⁰⁺ n σ a =
    eq-ℝ⁰⁺ _ _ (preserves-sum-permutation-fin-sequence-ℝ n σ (real-ℝ⁰⁺ ∘ a))
```

### If `aᵢ ≤ bᵢ` for all `i`, then the sum of the `aᵢ` is less than or equal to the sum of the `bᵢ`

```agda
abstract
  preserves-leq-sum-fin-sequence-ℝ⁰⁺ :
    {l1 l2 : Level} →
    (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l1) n) (b : fin-sequence (ℝ⁰⁺ l2) n) →
    ((i : Fin n) → leq-ℝ⁰⁺ (a i) (b i)) →
    leq-ℝ⁰⁺ (sum-fin-sequence-ℝ⁰⁺ n a) (sum-fin-sequence-ℝ⁰⁺ n b)
  preserves-leq-sum-fin-sequence-ℝ⁰⁺ n a b aᵢ≤bᵢ =
    preserves-leq-sum-fin-sequence-ℝ n (real-ℝ⁰⁺ ∘ a) (real-ℝ⁰⁺ ∘ b) aᵢ≤bᵢ
```

### If `aₙ` is nonnegative for all `n`, and `∑ aₙ = 0`, then `aₙ = 0` for all `n`

```agda
abstract
  is-all-zero-eq-zero-sum-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l) n) →
    (sum-fin-sequence-ℝ⁰⁺ n a ＝ raise-ℝ⁰⁺ l zero-ℝ⁰⁺) →
    (i : Fin n) → a i ＝ raise-ℝ⁰⁺ l zero-ℝ⁰⁺
  is-all-zero-eq-zero-sum-fin-sequence-ℝ⁰⁺ {l} n a ∑aₙ=0 i =
    eq-ℝ⁰⁺ _ _
      ( antisymmetric-leq-ℝ
        ( real-ℝ⁰⁺ (a i))
        ( raise-zero-ℝ l)
        {!   !}
        {!  preserves-leq-left-sim-ℝ (sim-raise-ℝ l zero-ℝ) !})
```
