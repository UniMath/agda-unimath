# The ratio test for series in the real numbers

```agda
module analysis.ratio-test-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.absolute-convergence-series-real-numbers
open import analysis.convergent-series-real-numbers
open import analysis.series-real-numbers

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.geometric-sequences-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

To prove that a [series](analysis.series-real-banach-spaces.md) `∑ aₙ` of
[real numbers](real-numbers.dedekind-real-numbers.md)
[converges](analysis.series-real-numbers.md), it is sufficient to show that
[there exists](foundation.existential-quantification.md) a
[natural number](elementary-number-theory.natural-numbers.md) `N` and a
[nonnegative](real-numbers.nonnegative-real-numbers.md) real number `r`
[less than](real-numbers.strict-inequality-real-numbers.md) 1 such that for all
`n ≥ N`, `|aₙ₊₁| ≤ r|aₙ|`.

## Definition

```agda
module _
  {l1 : Level} (l2 : Level)
  (σ : series-ℝ l1)
  where

  ratio-test-prop-series-ℝ : Prop (l1 ⊔ lsuc l2)
  ratio-test-prop-series-ℝ =
    ∃ ( ℕ × ℝ⁰⁺ l2)
      ( λ (N , r) →
        ( le-prop-ℝ (real-ℝ⁰⁺ r) one-ℝ) ∧
        Π-Prop
          ( ℕ)
          ( λ n →
            hom-Prop
              ( leq-ℕ-Prop N n)
              ( leq-prop-ℝ
                ( abs-ℝ (term-series-ℝ σ (succ-ℕ n)))
                ( real-ℝ⁰⁺ r *ℝ abs-ℝ (term-series-ℝ σ n)))))

  ratio-test-series-ℝ : UU (l1 ⊔ lsuc l2)
  ratio-test-series-ℝ = type-Prop ratio-test-prop-series-ℝ
```

## Properties

### The ratio test implies convergence

```agda
module _
  {l1 l2 : Level}
  (σ : series-ℝ l1)
  where

  abstract
    is-convergent-ratio-test-series-ℝ :
      {l2 : Level} → ratio-test-series-ℝ l2 σ → is-convergent-series-ℝ σ
    is-convergent-ratio-test-series-ℝ H =
      let
        open do-syntax-trunc-Prop (is-convergent-prop-series-ℝ σ)
      in do
        ((N , r) , K) ← H
        is-convergent-is-absolutely-convergent-series-ℝ
          ( σ)
          ( is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ
            ( map-abs-series-ℝ σ)
            {!   !}
            {!   !}
            {!   !})
```
