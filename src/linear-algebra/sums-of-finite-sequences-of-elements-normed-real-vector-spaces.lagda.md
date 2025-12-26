# Sums of finite sequences of elements in normed real vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.universe-levels

open import functional-analysis.normed-real-vector-spaces

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of a finite sequence of elements of a normed vector space over ℝ" Agda=sum-fin-sequence-type-Normed-ℝ-Vector-Space}}
of a [finite sequence](lists.finite-sequences.md) of elements of a
[normed vector space](functional-analysis.normed-real-vector-spaces.md) over the
[real numbers](real-numbers.dedekind-real-numbers.md) is the
[sum of the sequence](group-theory.sums-of-finite-sequences-of-elements-abelian-groups.md)
in the [abelian group](group-theory.abelian-groups.md) of the vector space under
addition.

## Definition

```agda
sum-fin-sequence-type-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) (n : ℕ) →
  fin-sequence (type-Normed-ℝ-Vector-Space V) n → type-Normed-ℝ-Vector-Space V
sum-fin-sequence-type-Normed-ℝ-Vector-Space V =
  sum-fin-sequence-type-Ab (ab-Normed-ℝ-Vector-Space V)
```

## Properties

### The norm of the sum of a finite sequence is at most the sum of the norms of the terms of the sequence

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (σ : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      leq-ℝ
        ( map-norm-Normed-ℝ-Vector-Space V
          ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n σ))
        ( sum-fin-sequence-ℝ n (map-norm-Normed-ℝ-Vector-Space V ∘ σ))
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space 0 σ =
      leq-eq-ℝ (eq-zero-norm-zero-Normed-ℝ-Vector-Space V)
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
      (succ-ℕ n) σ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          map-norm-Normed-ℝ-Vector-Space V
            ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V (succ-ℕ n) σ)
          ≤ ( map-norm-Normed-ℝ-Vector-Space V
              ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V
                ( n)
                ( σ ∘ inl-Fin n))) +ℝ
            ( map-norm-Normed-ℝ-Vector-Space V (σ (neg-one-Fin n)))
            by triangular-norm-Normed-ℝ-Vector-Space V _ _
          ≤ sum-fin-sequence-ℝ (succ-ℕ n) (map-norm-Normed-ℝ-Vector-Space V ∘ σ)
            by
              preserves-leq-right-add-ℝ _ _ _
                ( triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
                  ( n)
                  ( σ ∘ inl-Fin n))
```
