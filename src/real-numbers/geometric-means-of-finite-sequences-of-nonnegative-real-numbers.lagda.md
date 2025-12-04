# Geometric means of finite sequences of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.geometric-means-of-finite-sequences-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-natural-roots-nonnegative-real-numbers
open import real-numbers.products-of-finite-sequences-of-nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "geometric mean" WDID=Q185049 WD="geometric mean" Disambiguation="of a finite sequence of nonnegative real numbers" Agda=geometric-mean-fin-sequence-ℝ⁰⁺}}
of a nonempty [finite sequence](lists.finite-sequences.md) of
[nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) `a₁, ..., aₙ` is the `n`th
[root](real-numbers.nonzero-natural-roots-nonnegative-real-numbers.md) of the
[product](real-numbers.products-of-finite-sequences-of-nonnegative-real-numbers.md)
of the `aᵢ`.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ⁺)
  (a : fin-sequence (ℝ⁰⁺ l) (nat-ℕ⁺ n))
  where

  geometric-mean-fin-sequence-ℝ⁰⁺ : ℝ⁰⁺ l
  geometric-mean-fin-sequence-ℝ⁰⁺ =
    nonzero-nat-root-ℝ⁰⁺ n (product-fin-sequence-ℝ⁰⁺ (nat-ℕ⁺ n) a)
```
