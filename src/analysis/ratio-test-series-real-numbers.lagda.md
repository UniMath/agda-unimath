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
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.geometric-sequences-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

To prove that a [series](analysis.series-real-banach-spaces.md) `∑ aₙ` of
[real numbers](real-numbers.dedekind-real-numbers.md)
[converges](analysis.series-real-numbers.md), it is sufficient to show that
[there exists](foundation.existential-quantification.md) a
[nonnegative](real-numbers.nonnegative-real-numbers.md) real number `r`
[less than](real-numbers.strict-inequality-real-numbers.md) 1 such that for all
`n ≥ N`, `|aₙ₊₁| ≤ r|aₙ|`.

## Definition

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  ratio-test-prop-series-ℝ : Prop (lsuc l)
  ratio-test-prop-series-ℝ =
    ∃ ( ℝ⁰⁺ l)
      ( λ r →
        le-prop-ℝ (real-ℝ⁰⁺ r) one-ℝ ∧
        Π-Prop
          ( ℕ)
          ( λ n →
            ( leq-prop-ℝ
              ( abs-ℝ (term-series-ℝ σ (succ-ℕ n)))
              ( real-ℝ⁰⁺ r *ℝ abs-ℝ (term-series-ℝ σ n)))))

  ratio-test-series-ℝ : UU (lsuc l)
  ratio-test-series-ℝ = type-Prop ratio-test-prop-series-ℝ
```

## Properties

### The ratio test implies convergence

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  abstract
    is-convergent-ratio-test-series-ℝ :
      ratio-test-series-ℝ σ → is-convergent-series-ℝ σ
    is-convergent-ratio-test-series-ℝ H =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open do-syntax-trunc-Prop (is-convergent-prop-series-ℝ σ)
      in do
        (r⁰⁺@(r , 0≤r) , r<1 , K) ← H
        let |σ₀| = abs-ℝ (term-series-ℝ σ 0)
        is-convergent-is-absolutely-convergent-series-ℝ
          ( σ)
          ( is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ
            ( map-abs-series-ℝ σ)
            ( convergent-standard-geometric-series-ℝ
              ( |σ₀|)
              ( r)
              ( inv-tr (λ x → le-ℝ x one-ℝ) (abs-real-ℝ⁰⁺ r⁰⁺) r<1))
            ( λ _ → is-nonnegative-abs-ℝ _)
            ( ind-ℕ
              ( refl-leq-ℝ _)
              ( λ n |σₙ|≤arⁿ →
                chain-of-inequalities
                  abs-ℝ (term-series-ℝ σ (succ-ℕ n))
                  ≤ r *ℝ abs-ℝ (term-series-ℝ σ n)
                    by K n
                  ≤ r *ℝ seq-standard-geometric-sequence-ℝ |σ₀| r n
                    by preserves-leq-left-mul-ℝ⁰⁺ r⁰⁺ |σₙ|≤arⁿ
                  ≤ r *ℝ (|σ₀| *ℝ power-ℝ n r)
                    by
                      leq-eq-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( compute-standard-geometric-sequence-ℝ |σ₀| r n))
                  ≤ |σ₀| *ℝ (r *ℝ power-ℝ n r)
                    by leq-eq-ℝ (left-swap-mul-ℝ _ _ _)
                  ≤ |σ₀| *ℝ power-ℝ (succ-ℕ n) r
                    by leq-eq-ℝ (ap-mul-ℝ refl (inv (power-succ-ℝ' n r)))
                  ≤ seq-standard-geometric-sequence-ℝ |σ₀| r (succ-ℕ n)
                    by
                      leq-eq-ℝ
                        ( inv
                          ( compute-standard-geometric-sequence-ℝ
                            ( |σ₀|)
                            ( r)
                            ( succ-ℕ n))))))
```
