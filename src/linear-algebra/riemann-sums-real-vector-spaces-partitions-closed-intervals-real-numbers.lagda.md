# Riemann sums in real vector spaces over partitions of closed intervals in the real numbers

```agda
module linear-algebra.riemann-sums-real-vector-spaces-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-real-vector-spaces

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a function `f` from a
[closed interval in the real numbers](real-numbers.closed-intervals-real-numbers.md)
`[a, b]` into a [real vector space](linear-algebra.real-vector-spaces.md) `V`,
the {{#concept "Riemann sum" WDID=Q1156903 WD="Riemann sum"}} of a
[partition](real-numbers.partitions-closed-intervals-real-numbers.md) `p`
consisting of the sequence `a = a₁ ≤ ... ≤ aₙ = b`, `S(p)` is the sum from
`k = 1` to `k = n - 1` of `(aᵢ₊₁ - aᵢ) * f(aᵢ)`.

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-ℝ-Vector-Space V)
  where

  riemann-sum-partition-closed-interval-ℝ-Vector-Space :
    partition-closed-interval-ℝ [a,b] → type-ℝ-Vector-Space V
  riemann-sum-partition-closed-interval-ℝ-Vector-Space
    p@((((succ-ℕ n , u) , _) , is-increasing-u) , u₋₁=a , u₀=b) =
    sum-fin-sequence-type-ℝ-Vector-Space V n
      ( λ i →
        mul-ℝ-Vector-Space
          ( V)
          ( u (inl-Fin n i) -ℝ u (skip-zero-Fin n i))
          ( f (fin-sequence-partition-closed-interval-ℝ [a,b] p (inl-Fin n i))))
```

## External links

- [Riemann sum](https://en.wikipedia.org/wiki/Riemann_sum) on Wikipedia
