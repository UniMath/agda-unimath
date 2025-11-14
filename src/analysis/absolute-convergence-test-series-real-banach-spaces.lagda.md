# The absolute convergence test for series in real Banach spaces

```agda
module analysis.absolute-convergence-test-series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.convergent-series-real-banach-spaces
open import analysis.convergent-series-real-numbers
open import analysis.series-real-banach-spaces
open import analysis.series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces

open import metric-spaces.cauchy-sequences-metric-spaces

open import real-numbers.metric-additive-group-of-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A [series](analysis.series-real-banach-spaces.md) `Σ aₙ` in a
[real Banach space](linear-algebra.real-banach-spaces.md) is said to
{{#concept "absolutely converge" WDID=Q332465 WD="absolute convergence" Agda=absolutely-converges-prop-series-ℝ-Banach-Space Disambiguation="in a real Banach space"}}
if the series of its norms `Σ ∥aₙ∥` converges in the
[real numbers](real-numbers.dedekind-real-numbers.md).

This is a sufficient, but not necessary, condition for a series to
[converge](analysis.convergent-series-real-banach-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-absolutely-convergent-prop-series-ℝ-Banach-Space : Prop (lsuc l1)
  is-absolutely-convergent-prop-series-ℝ-Banach-Space =
    is-convergent-prop-series-ℝ
      ( series-terms-ℝ
        ( map-norm-ℝ-Banach-Space V ∘ term-series-ℝ-Banach-Space V σ))

  is-absolutely-convergent-series-ℝ-Banach-Space : UU (lsuc l1)
  is-absolutely-convergent-series-ℝ-Banach-Space =
    type-Prop is-absolutely-convergent-prop-series-ℝ-Banach-Space
```

## Properties

### If a series is absolutely convergent, it is convergent

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  abstract
    is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space :
      is-absolutely-convergent-series-ℝ-Banach-Space V σ →
      is-convergent-series-ℝ-Banach-Space V σ
    is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space
      (sum-norm , converges-sum-norm) =
      let
        open do-syntax-trunc-Prop (is-convergent-prop-series-ℝ-Banach-Space V σ)
      in do
        convergence-modulus-norm ← converges-sum-norm
        let
          cauchy-modulus-sum-norm =
            is-cauchy-has-limit-modulus-sequence-Metric-Space
              ( metric-space-ℝ l1)
              ( partial-sum-series-ℝ
                ( series-terms-ℝ
                  ( map-norm-ℝ-Banach-Space V ∘
                    term-series-ℝ-Banach-Space V σ)))
              ( sum-norm)
              ( convergence-modulus-norm)
          cauchy-modulus-sum :
            is-cauchy-sequence-ℝ-Banach-Space
              ( V)
              ( partial-sum-series-ℝ-Banach-Space V σ)
          cauchy-modulus-sum ε =
            let
              (N , cauchy-modulus-ε-N) = cauchy-modulus-sum-norm ε
              lemma : (n k : ℕ) → {!   !}
            in
              ( N ,
                {!   !})
        {!   !}
```
