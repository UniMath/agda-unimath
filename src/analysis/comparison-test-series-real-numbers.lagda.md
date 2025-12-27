# Comparison test for series in the real numbers

```agda
module analysis.comparison-test-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-numbers
open import analysis.nonnegative-series-real-numbers
open import analysis.series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.cauchy-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [series](analysis.series-real-numbers.md) `∑ aₙ` of
[nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md)
[converges](analysis.convergent-series-real-numbers.md) if there
[exists](foundation.existential-quantification.md) a convergent series `∑ bₙ`
such that `aₙ ≤ bₙ` for all `n`. This is the
{{#concept "comparison test" Disambiguation="for series in the real numbers" Agda=comparison-test-series-ℝ Agda=is-convergent-comparison-test-series-ℝ}} for series in the real numbers.

## Definition

```agda
module _
  {l1 : Level}
  (l2 : Level)
  (σ : series-ℝ l1)
  where

  comparison-test-prop-series-ℝ : Prop (l1 ⊔ lsuc l2)
  comparison-test-prop-series-ℝ =
    ( is-nonnegative-prop-series-ℝ σ) ∧
    ( ∃
      ( convergent-series-ℝ l2)
      ( λ τ →
        Π-Prop
          ( ℕ)
          ( λ n →
            leq-prop-ℝ (term-series-ℝ σ n) (term-convergent-series-ℝ τ n))))

  comparison-test-series-ℝ : UU (l1 ⊔ lsuc l2)
  comparison-test-series-ℝ =
    type-Prop comparison-test-prop-series-ℝ
```

## Properties

### The comparison test implies convergence

```agda
module _
  {l1 l2 : Level}
  (σ : series-ℝ l1)
  (τ : convergent-series-ℝ l2)
  where

  abstract
    is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ :
      ((n : ℕ) → is-nonnegative-ℝ (term-series-ℝ σ n)) →
      ((n : ℕ) → leq-ℝ (term-series-ℝ σ n) (term-convergent-series-ℝ τ n)) →
      is-convergent-series-ℝ σ
    is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ 0≤σₙ σₙ≤τₙ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open do-syntax-trunc-Prop (is-convergent-prop-series-ℝ σ)
      in do
        lim-modulus-τ ← is-sum-sum-convergent-series-ℝ τ
        let
          cauchy-mod-partial-sum-τ =
            is-cauchy-has-limit-modulus-sequence-Metric-Space
              ( metric-space-ℝ l2)
              ( partial-sum-convergent-series-ℝ τ)
              ( sum-convergent-series-ℝ τ)
              ( lim-modulus-τ)
          μ = pr1 ∘ cauchy-mod-partial-sum-τ
          is-mod-μ = pr2 ∘ cauchy-mod-partial-sum-τ
          is-mod'-μ ε n k με≤n =
            neighborhood-dist-ℝ ε _ _
              ( leq-dist-leq-diff-ℝ _ _ _
                ( chain-of-inequalities
                  partial-sum-series-ℝ σ (n +ℕ k) -ℝ partial-sum-series-ℝ σ n
                  ≤ partial-sum-series-ℝ (drop-series-ℝ n σ) k
                    by leq-eq-ℝ (inv (partial-sum-drop-series-ℝ n σ k))
                  ≤ partial-sum-series-ℝ
                      ( drop-series-ℝ n (series-convergent-series-ℝ τ))
                      ( k)
                    by
                      leq-sum-fin-sequence-ℝ k _ _
                        ( λ m → σₙ≤τₙ (n +ℕ nat-Fin k m))
                  ≤ ( partial-sum-convergent-series-ℝ τ (n +ℕ k)) -ℝ
                    ( partial-sum-convergent-series-ℝ τ n)
                    by
                      leq-eq-ℝ
                        ( partial-sum-drop-series-ℝ
                          ( n)
                          ( series-convergent-series-ℝ τ)
                          ( k))
                  ≤ dist-ℝ
                      ( partial-sum-convergent-series-ℝ τ (n +ℕ k))
                      ( partial-sum-convergent-series-ℝ τ n)
                    by leq-diff-dist-ℝ _ _
                  ≤ real-ℚ⁺ ε
                    by
                      leq-dist-neighborhood-ℝ ε _ _
                        ( is-mod-μ
                          ( ε)
                          ( n +ℕ k)
                          ( n)
                          ( transitive-leq-ℕ
                            ( μ ε)
                            ( n)
                            ( n +ℕ k)
                            ( leq-add-ℕ n k)
                            ( με≤n))
                          ( με≤n)))
                ( transitive-leq-ℝ
                  ( partial-sum-series-ℝ σ n -ℝ partial-sum-series-ℝ σ (n +ℕ k))
                  ( zero-ℝ)
                  ( real-ℚ⁺ ε)
                  ( is-nonnegative-real-ℝ⁰⁺ (nonnegative-real-ℚ⁺ ε))
                  ( binary-tr
                    ( leq-ℝ)
                    ( distributive-neg-diff-ℝ _ _)
                    ( neg-zero-ℝ)
                    ( neg-leq-ℝ
                      ( is-nonnegative-diff-leq-ℝ
                        ( is-increasing-partial-sum-is-nonnegative-term-series-ℝ
                          ( σ)
                          ( 0≤σₙ)
                          ( n)
                          ( n +ℕ k)
                          ( leq-add-ℕ n k)))))))
        is-convergent-is-cauchy-sequence-partial-sum-series-ℝ
          σ
          ( λ ε →
            ( μ ε ,
              is-cauchy-modulus-is-cauchy-modulus-sequence-Metric-Space'
                ( metric-space-ℝ l1)
                ( partial-sum-series-ℝ σ)
                ( ε)
                ( μ ε)
                ( is-mod'-μ ε)))

module _
  {l1 l2 : Level}
  (σ : series-ℝ l1)
  where

  is-convergent-comparison-test-series-ℝ :
    {l2 : Level} → comparison-test-series-ℝ l2 σ → is-convergent-series-ℝ σ
  is-convergent-comparison-test-series-ℝ (0≤σₙ , ∃τ) =
    rec-trunc-Prop
      ( is-convergent-prop-series-ℝ σ)
      ( λ (τ , σₙ≤τₙ) →
        is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ
          ( σ)
          ( τ)
          ( 0≤σₙ)
          ( σₙ≤τₙ))
      ( ∃τ)
```

## External links

- [Direct comparison test](https://en.wikipedia.org/wiki/Direct_comparison_test)
  on Wikipedia
