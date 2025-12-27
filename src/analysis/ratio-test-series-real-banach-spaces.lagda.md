# The ratio test for series in real Banach spaces

```agda
module analysis.ratio-test-series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.absolute-convergence-series-real-banach-spaces
open import analysis.convergent-series-real-banach-spaces
open import analysis.ratio-test-series-real-numbers
open import analysis.series-real-banach-spaces

open import elementary-number-theory.natural-numbers

open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces

open import logic.functoriality-existential-quantification

open import real-numbers.absolute-value-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
```

</details>

## Idea

To prove that a [series](analysis.series-real-banach-spaces.md) `∑ aₙ` in a
[real Banach space](linear-algebra.real-banach-spaces.md)
[converges](analysis.series-real-numbers.md), it is sufficient to show that
[there exists](foundation.existential-quantification.md) a
[nonnegative](real-numbers.nonnegative-real-numbers.md) real number `r`
[less than](real-numbers.strict-inequality-real-numbers.md) 1 such that for all
`n`, `∥aₙ₊₁∥ ≤ r∥aₙ∥`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  ratio-test-prop-series-ℝ-Banach-Space : Prop (lsuc l1)
  ratio-test-prop-series-ℝ-Banach-Space =
    ∃ ( ℝ⁰⁺ l1)
      ( λ r →
        le-prop-ℝ⁰⁺ r one-ℝ⁰⁺ ∧
        Π-Prop
          ( ℕ)
          ( λ n →
            leq-prop-ℝ
              ( map-norm-ℝ-Banach-Space V
                ( term-series-ℝ-Banach-Space V σ (succ-ℕ n)))
              ( ( real-ℝ⁰⁺ r) *ℝ
                ( map-norm-ℝ-Banach-Space V
                  ( term-series-ℝ-Banach-Space V σ n)))))

  ratio-test-series-ℝ-Banach-Space : UU (lsuc l1)
  ratio-test-series-ℝ-Banach-Space =
    type-Prop ratio-test-prop-series-ℝ-Banach-Space
```

## Properties

### The ratio test implies convergence

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  abstract
    is-convergent-ratio-test-series-ℝ-Banach-Space :
      ratio-test-series-ℝ-Banach-Space V σ →
      is-convergent-series-ℝ-Banach-Space V σ
    is-convergent-ratio-test-series-ℝ-Banach-Space H =
      is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space
        ( V)
        ( σ)
        ( is-convergent-ratio-test-series-ℝ
          ( map-norm-series-ℝ-Banach-Space V σ)
          ( map-tot-exists
            ( λ r (r<1 , K) →
              ( r<1 ,
                λ n →
                binary-tr
                  ( leq-ℝ)
                  ( inv (abs-real-ℝ⁰⁺ (nonnegative-norm-ℝ-Banach-Space V _)))
                  ( ap-mul-ℝ
                    ( refl)
                    ( inv
                      ( abs-real-ℝ⁰⁺ (nonnegative-norm-ℝ-Banach-Space V _))))
                  ( K n)))
            ( H)))
```

## See also

- [The ratio test for series of real numbers](analysis.ratio-test-series-real-numbers.md)
