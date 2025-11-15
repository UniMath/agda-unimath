# Convergent series in the real numbers

```agda
module analysis.convergent-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cauchy-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [series of real numbers](analysis.series-real-numbers.md) is
{{#concept "convergent" Disambiguation="series in ℝ" Agda=is-convergent-series-ℝ Agda=convergent-series-ℝ WDID=Q1211057 WD="convergent series"}}
if its partial sums converge in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-sum-prop-series-ℝ : ℝ l → Prop l
  is-sum-prop-series-ℝ = is-sum-prop-series-Metric-Ab σ

  is-sum-series-ℝ : ℝ l → UU l
  is-sum-series-ℝ = is-sum-series-Metric-Ab σ

  is-convergent-prop-series-ℝ : Prop (lsuc l)
  is-convergent-prop-series-ℝ =
    is-convergent-prop-series-Metric-Ab σ

  is-convergent-series-ℝ : UU (lsuc l)
  is-convergent-series-ℝ = is-convergent-series-Metric-Ab σ

convergent-series-ℝ : (l : Level) → UU (lsuc l)
convergent-series-ℝ l = type-subtype (is-convergent-prop-series-ℝ {l})

module _
  {l : Level}
  (σ : convergent-series-ℝ l)
  where

  series-convergent-series-ℝ : series-ℝ l
  series-convergent-series-ℝ = pr1 σ

  term-convergent-series-ℝ : sequence (ℝ l)
  term-convergent-series-ℝ = term-series-ℝ series-convergent-series-ℝ

  sum-convergent-series-ℝ : ℝ l
  sum-convergent-series-ℝ = pr1 (pr2 σ)

  is-sum-sum-convergent-series-ℝ :
    is-sum-series-ℝ series-convergent-series-ℝ sum-convergent-series-ℝ
  is-sum-sum-convergent-series-ℝ = pr2 (pr2 σ)

  partial-sum-convergent-series-ℝ : sequence (ℝ l)
  partial-sum-convergent-series-ℝ =
    partial-sum-series-ℝ series-convergent-series-ℝ
```

## Properties

### If the partial sums of a series form a Cauchy sequence, the series converges

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ :
    is-cauchy-sequence-ℝ (partial-sum-series-ℝ σ) →
    is-convergent-series-ℝ σ
  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ =
    is-convergent-is-cauchy-sequence-partial-sum-series-Complete-Metric-Ab
      ( complete-metric-ab-add-ℝ l)
      ( σ)
```

### If a series is nonnegative and bounded by a convergent series, the series converges

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
                        ( is-monotonic-partial-sum-is-nonnegative-term-series-ℝ
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
```
