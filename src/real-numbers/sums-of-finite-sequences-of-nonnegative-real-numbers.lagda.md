# Sums of finite sequences of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
open import real-numbers.zero-nonnegative-real-numbers

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

### If `aₙ` is nonnegative for all `n`, `aᵢ ≤ ∑ aₙ`

```agda
abstract
  leq-term-sum-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l) n) (i : Fin n) →
    leq-ℝ⁰⁺ (a i) (sum-fin-sequence-ℝ⁰⁺ n a)
  leq-term-sum-fin-sequence-ℝ⁰⁺ (succ-ℕ n) a (inr star) =
    leq-right-add-real-ℝ⁰⁺
      ( real-ℝ⁰⁺ (a (neg-one-Fin n)))
      ( sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl-Fin n))
  leq-term-sum-fin-sequence-ℝ⁰⁺ (succ-ℕ n) a (inl i) =
    transitive-leq-ℝ
      ( real-ℝ⁰⁺ (a (inl i)))
      ( real-sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl))
      ( real-sum-fin-sequence-ℝ⁰⁺ (succ-ℕ n) a)
      ( leq-left-add-real-ℝ⁰⁺
        ( real-sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl))
        ( a (inr star)))
      ( leq-term-sum-fin-sequence-ℝ⁰⁺ n (a ∘ inl) i)
```

### If `aₙ` is nonnegative for all `n`, and `∑ aₙ = 0`, then `aₙ = 0` for all `n`

```agda
abstract
  is-all-zero-is-zero-sum-fin-sequence-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (a : fin-sequence (ℝ⁰⁺ l) n) →
    is-zero-ℝ⁰⁺ (sum-fin-sequence-ℝ⁰⁺ n a) →
    (i : Fin n) → is-zero-ℝ⁰⁺ (a i)
  is-all-zero-is-zero-sum-fin-sequence-ℝ⁰⁺ {l} n a ∑aᵢ=0 i =
    is-zero-leq-zero-ℝ⁰⁺
      ( a i)
      ( transitive-leq-ℝ⁰⁺
        ( a i)
        ( sum-fin-sequence-ℝ⁰⁺ n a)
        ( zero-ℝ⁰⁺)
        ( leq-zero-is-zero-ℝ⁰⁺ (sum-fin-sequence-ℝ⁰⁺ n a) ∑aᵢ=0)
        ( leq-term-sum-fin-sequence-ℝ⁰⁺ n a i))
```

### The sum of a finite sequence of two nonnegative real numbers is the result of adding them

```agda
abstract
  compute-sum-two-ℝ⁰⁺ :
    {l : Level} (f : fin-sequence (ℝ⁰⁺ l) 2) →
    sum-fin-sequence-ℝ⁰⁺ 2 f ＝ f (zero-Fin 1) +ℝ⁰⁺ f (one-Fin 1)
  compute-sum-two-ℝ⁰⁺ f =
    eq-ℝ⁰⁺ _ _ (compute-sum-two-ℝ (real-ℝ⁰⁺ ∘ f))
```
