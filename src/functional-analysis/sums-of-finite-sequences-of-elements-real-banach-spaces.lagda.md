# Sums of finite sequences of elements in real Banach spaces

```agda
module functional-analysis.sums-of-finite-sequences-of-elements-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.universe-levels

open import functional-analysis.real-banach-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-normed-real-vector-spaces

open import lists.finite-sequences

open import real-numbers.inequality-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of a finite sequence of elements of a real Banach space" Agda=sum-fin-sequence-type-ℝ-Banach-Space}}
of a [finite sequence](lists.finite-sequences.md) of elements of a
[real Banach space](functional-analysis.real-banach-spaces.md) is the
[sum of the sequence](group-theory.sums-of-finite-sequences-of-elements-abelian-groups.md)
in the [abelian group](group-theory.abelian-groups.md) of the space under
addition.

## Definition

```agda
sum-fin-sequence-type-ℝ-Banach-Space :
  {l1 l2 : Level} (V : ℝ-Banach-Space l1 l2) →
  (n : ℕ) → fin-sequence (type-ℝ-Banach-Space V) n → type-ℝ-Banach-Space V
sum-fin-sequence-type-ℝ-Banach-Space V =
  sum-fin-sequence-type-Normed-ℝ-Vector-Space
    ( normed-vector-space-ℝ-Banach-Space V)
```

## Properties

### The norm of the sum of a finite sequence is at most the sum of the norms of the terms of the sequence

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  where

  abstract
    triangle-inequality-norm-sum-fin-sequence-type-ℝ-Banach-Space :
      (n : ℕ) (σ : fin-sequence (type-ℝ-Banach-Space V) n) →
      leq-ℝ
        ( map-norm-ℝ-Banach-Space V
          ( sum-fin-sequence-type-ℝ-Banach-Space V n σ))
        ( sum-fin-sequence-ℝ n (map-norm-ℝ-Banach-Space V ∘ σ))
    triangle-inequality-norm-sum-fin-sequence-type-ℝ-Banach-Space =
      triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
        ( normed-vector-space-ℝ-Banach-Space V)
```
