# The real number `e`

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.e-real-number where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-numbers
open import analysis.ratio-test-series-real-numbers
open import analysis.series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The constant `e` is defined to be the sum of the infinite
[series](analysis.series-real-numbers.md) $∑_{n=0}^{∞} \frac{1}{n!}$, which can
be shown to converge by
[the ratio test](analysis.ratio-test-series-real-numbers.md).

## Definition

```agda
e-series-ℝ : series-ℝ lzero
e-series-ℝ =
  series-terms-ℝ (λ n → real-ℚ (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n)))

is-convergent-e-series-ℝ : is-convergent-series-ℝ e-series-ℝ
is-convergent-e-series-ℝ =
  let
    open inequality-reasoning-Large-Poset ℝ-Large-Poset
  in
    is-convergent-is-convergent-drop-series-ℝ e-series-ℝ 1
      ( is-convergent-ratio-test-series-ℝ
        ( drop-series-ℝ 1 e-series-ℝ)
        ( intro-exists
          ( nonnegative-real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ (2 , λ ())))
          ( preserves-le-real-ℚ
              ( tr
                ( le-ℚ _)
                ( ap rational-ℚ⁺ inv-one-ℚ⁺)
                ( inv-le-ℚ⁺ _ _ (preserves-le-rational-ℕ {1} {2} _))) ,
            λ n →
              chain-of-inequalities
                abs-ℝ
                  ( real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ
                        ( succ-ℕ (1 +ℕ n)))))
                ≤ abs-ℝ
                    ( real-ℚ⁺
                      ( positive-reciprocal-rational-ℕ⁺
                        ( nonzero-factorial-ℕ
                          ( succ-ℕ (succ-ℕ n)))))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( ( abs-ℝ) ∘
                          ( real-ℚ⁺) ∘
                          ( positive-reciprocal-rational-ℕ⁺) ∘
                          ( nonzero-factorial-ℕ) ∘
                          ( succ-ℕ))
                        ( commutative-add-ℕ 1 n))
                ≤ real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ
                        ( succ-ℕ (succ-ℕ n))))
                  by
                    leq-eq-ℝ
                      ( abs-real-ℝ⁺
                        ( positive-real-ℚ⁺
                          ( positive-reciprocal-rational-ℕ⁺
                            ( nonzero-factorial-ℕ
                              ( succ-ℕ (succ-ℕ n))))))
                ≤ real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ (succ-ℕ n) *ℕ⁺ (2 , λ ())))
                  by
                    preserves-leq-real-ℚ
                      ( inv-leq-ℚ⁺ _ _
                        ( preserves-leq-rational-ℕ
                          ( preserves-leq-right-mul-ℕ
                            ( factorial-ℕ (succ-ℕ n))
                            ( 2)
                            ( succ-ℕ (succ-ℕ n))
                            ( _))))
                ≤ real-ℚ⁺
                    ( inv-ℚ⁺
                      ( ( positive-rational-ℕ⁺
                          ( nonzero-factorial-ℕ (succ-ℕ n))) *ℚ⁺
                        ( positive-rational-ℕ⁺ (2 , λ ()))))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( real-ℚ⁺ ∘ inv-ℚ⁺)
                        ( eq-ℚ⁺ (inv (mul-rational-ℕ _ _))))
                ≤ real-ℚ⁺
                    ( ( positive-reciprocal-rational-ℕ⁺
                        ( nonzero-factorial-ℕ (succ-ℕ n))) *ℚ⁺
                      ( positive-reciprocal-rational-ℕ⁺ (2 , (λ ()))))
                  by leq-eq-ℝ (ap real-ℚ⁺ (distributive-inv-mul-ℚ⁺ _ _))
                ≤ ( real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ (succ-ℕ n)))) *ℝ
                  ( real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ (2 , λ ())))
                  by leq-eq-ℝ (inv (mul-real-ℚ _ _))
                ≤ ( real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ (2 , λ ()))) *ℝ
                  ( real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ (succ-ℕ n))))
                  by leq-eq-ℝ (commutative-mul-ℝ _ _)
                ≤ ( real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ (2 , λ ()))) *ℝ
                  ( real-ℚ⁺
                    ( positive-reciprocal-rational-ℕ⁺
                      ( nonzero-factorial-ℕ (1 +ℕ n))))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( refl)
                        ( ap
                          ( ( real-ℚ⁺) ∘
                            ( positive-reciprocal-rational-ℕ⁺) ∘
                            ( nonzero-factorial-ℕ))
                          ( commutative-add-ℕ n 1)))
                ≤ ( real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ (2 , λ ()))) *ℝ
                  ( abs-ℝ
                    ( real-ℚ⁺
                      ( positive-reciprocal-rational-ℕ⁺
                        ( nonzero-factorial-ℕ (1 +ℕ n)))))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( refl)
                        ( inv
                          ( abs-real-ℝ⁺
                            ( positive-real-ℚ⁺
                              ( positive-reciprocal-rational-ℕ⁺
                                ( nonzero-factorial-ℕ (1 +ℕ n))))))))))

convergent-e-series-ℝ : convergent-series-ℝ lzero
convergent-e-series-ℝ = (e-series-ℝ , is-convergent-e-series-ℝ)

e-ℝ : ℝ lzero
e-ℝ = sum-convergent-series-ℝ convergent-e-series-ℝ
```
