# The exponential power series in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.exponential-power-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-numbers
open import analysis.power-series-at-zero-real-numbers
open import analysis.ratio-test-series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
[natural exponential function](analysis.exponential-function-real-numbers.md) on
the [real numbers](real-numbers.dedekind-real-numbers.md) is defined by the
[power series at zero](analysis.power-series-at-zero-real-numbers.md)
$$∑_{n=0}^{∞} \frac{x^n}{n!}$$

This page describes properties of the power series.

## Definition

```agda
exp-power-series-at-zero-ℝ : (l : Level) → power-series-at-zero-ℝ l
exp-power-series-at-zero-ℝ l =
  power-series-at-zero-coefficients-ℝ
    ( λ n → raise-real-ℚ l (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n)))

term-at-point-exp-power-series-at-zero-ℝ : {l : Level} → ℝ l → sequence (ℝ l)
term-at-point-exp-power-series-at-zero-ℝ =
  term-at-point-power-series-at-zero-ℝ (exp-power-series-at-zero-ℝ _)
```

## Properties

### The ratio of successive terms

```agda
abstract
  ratio-successive-term-power-series-at-zero-ℝ :
    {l : Level} (x : ℝ l) (n : ℕ) →
    term-at-point-exp-power-series-at-zero-ℝ x (succ-ℕ n) ＝
    ( x *ℝ real-ℚ (reciprocal-rational-succ-ℕ n)) *ℝ
    ( term-at-point-exp-power-series-at-zero-ℝ x n)
  ratio-successive-term-power-series-at-zero-ℝ {l} x n =
    equational-reasoning
      term-at-point-exp-power-series-at-zero-ℝ x (succ-ℕ n)
      ＝
        ( raise-real-ℚ⁺
          ( l)
          ( inv-ℚ⁺
            ( positive-rational-ℕ⁺
              ( nonzero-factorial-ℕ n *ℕ⁺ succ-nonzero-ℕ' n)))) *ℝ
        ( power-ℝ n x *ℝ x)
        by
          ap-mul-ℝ
            ( ap
              ( raise-real-ℚ⁺ l ∘ inv-ℚ⁺ ∘ positive-rational-ℕ⁺)
              ( eq-nonzero-ℕ
                { nonzero-factorial-ℕ (succ-ℕ n)}
                { nonzero-factorial-ℕ n *ℕ⁺ succ-nonzero-ℕ' n}
                ( refl)))
            ( power-succ-ℝ n x)
      ＝
        ( raise-real-ℚ⁺
          ( l)
          ( inv-ℚ⁺
            ( ( positive-rational-ℕ⁺ (nonzero-factorial-ℕ n)) *ℚ⁺
              ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' n))))) *ℝ
        ( power-ℝ n x *ℝ x)
        by
          ap-mul-ℝ
            ( ap
              ( raise-real-ℚ⁺ l ∘ inv-ℚ⁺)
              ( inv (mul-positive-rational-ℕ⁺ _ _)))
            ( refl)
      ＝
        ( raise-real-ℚ
          ( l)
          ( reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n) *ℚ
            reciprocal-rational-succ-ℕ n)) *ℝ
        ( power-ℝ n x *ℝ x)
        by
          ap-mul-ℝ
            ( ap (raise-real-ℚ⁺ l) (distributive-inv-mul-ℚ⁺ _ _))
            ( refl)
      ＝
        ( raise-ℝ
          ( l)
          ( ( real-ℚ (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n))) *ℝ
            ( real-ℚ (reciprocal-rational-succ-ℕ n)))) *ℝ
        ( power-ℝ n x *ℝ x)
        by ap-mul-ℝ (ap (raise-ℝ l) (inv (mul-real-ℚ _ _))) refl
      ＝
        ( raise-real-ℚ l (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n))) *ℝ
        ( real-ℚ (reciprocal-rational-succ-ℕ n)) *ℝ
        ( power-ℝ n x *ℝ x)
        by ap-mul-ℝ (inv (mul-left-raise-ℝ l _ _)) refl
      ＝
        ( term-at-point-exp-power-series-at-zero-ℝ x n) *ℝ
        ( real-ℚ (reciprocal-rational-succ-ℕ n) *ℝ x)
        by interchange-law-mul-mul-ℝ _ _ _ _
      ＝
        ( real-ℚ (reciprocal-rational-succ-ℕ n) *ℝ x) *ℝ
        ( term-at-point-exp-power-series-at-zero-ℝ x n)
        by commutative-mul-ℝ _ _
      ＝
        ( x *ℝ real-ℚ (reciprocal-rational-succ-ℕ n)) *ℝ
        ( term-at-point-exp-power-series-at-zero-ℝ x n)
        by ap-mul-ℝ (commutative-mul-ℝ _ _) refl
```

### The exponential power series converges everywhere

```agda
abstract
  is-convergent-everywhere-exp-power-series-at-zero-ℝ :
    (l : Level) →
    is-convergent-everywhere-power-series-at-zero-ℝ
      ( exp-power-series-at-zero-ℝ l)
  is-convergent-everywhere-exp-power-series-at-zero-ℝ l x =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      open
        do-syntax-trunc-Prop
          ( is-convergent-at-point-prop-power-series-at-zero-ℝ
            ( exp-power-series-at-zero-ℝ l)
            ( x))
    in do
      (q , |x|<q) ← is-inhabited-upper-cut-ℝ (abs-ℝ x)
      (n' , q<n') ← exists-greater-natural-ℚ q
      let
        n = succ-ℕ n'
        n⁺ = succ-nonzero-ℕ' n'
      is-convergent-is-convergent-drop-series-ℝ
        ( compute-series-at-point-power-series-at-zero-ℝ
          ( exp-power-series-at-zero-ℝ l)
          ( x))
        ( n *ℕ 2)
        ( is-convergent-ratio-test-series-ℝ _
          ( intro-exists
            ( raise-ℝ⁰⁺
              ( l)
              ( nonnegative-real-ℚ⁰⁺
                ( nonnegative-ℚ⁺
                  ( positive-reciprocal-rational-ℕ⁺ two-ℕ⁺))))
            ( preserves-le-left-raise-ℝ
                ( l)
                ( preserves-le-real-ℚ
                  ( tr
                    ( le-ℚ _)
                    ( ap rational-ℚ⁺ inv-one-ℚ⁺)
                    ( inv-le-ℚ⁺ _ _
                      ( preserves-le-rational-ℕ {1} {2} _)))) ,
              λ k →
                chain-of-inequalities
                abs-ℝ
                  ( term-at-point-exp-power-series-at-zero-ℝ
                    ( x)
                    ( n *ℕ 2 +ℕ succ-ℕ k))
                ≤ abs-ℝ
                    ( ( x) *ℝ
                      ( real-ℚ (reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k))) *ℝ
                      ( term-at-point-exp-power-series-at-zero-ℝ
                        ( x)
                        ( n *ℕ 2 +ℕ k)))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( abs-ℝ)
                        ( ratio-successive-term-power-series-at-zero-ℝ x _))
                ≤ ( abs-ℝ x) *ℝ
                  ( abs-ℝ
                    ( real-ℚ (reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by leq-eq-ℝ (abs-mul-ℝ _ _ ∙ ap-mul-ℝ (abs-mul-ℝ _ _) refl)
                ≤ ( real-ℚ q) *ℝ
                  ( abs-ℝ
                    ( real-ℚ (reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ _)
                      ( preserves-leq-right-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ _)
                        ( leq-real-is-in-upper-cut-ℝ (abs-ℝ x) |x|<q))
                ≤ ( real-ℕ n) *ℝ
                  ( abs-ℝ
                    ( real-ℚ (reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ _)
                      ( preserves-leq-right-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ _)
                        ( preserves-leq-real-ℚ
                          ( leq-le-ℚ
                            ( transitive-le-ℚ _ _ _
                              ( preserves-le-rational-ℕ (succ-le-ℕ n'))
                              ( q<n')))))
                ≤ ( real-ℕ n) *ℝ
                  ( real-ℚ (reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( abs-real-ℝ⁺
                            ( positive-real-ℚ⁺
                              ( positive-reciprocal-rational-succ-ℕ _))))
                        ( refl))
                ≤ ( real-ℚ
                    ( ( rational-ℕ n) *ℚ
                      ( reciprocal-rational-succ-ℕ (n *ℕ 2 +ℕ k)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by leq-eq-ℝ (ap-mul-ℝ (mul-real-ℚ _ _) refl)
                ≤ ( real-ℚ
                    ( ( rational-ℕ n) *ℚ
                      ( reciprocal-rational-ℕ⁺ (n⁺ *ℕ⁺ two-ℕ⁺)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ _)
                      ( preserves-leq-real-ℚ
                        ( preserves-leq-left-mul-ℚ⁺
                          ( positive-rational-ℕ⁺ n⁺)
                          ( _)
                          ( _)
                          ( inv-leq-ℚ⁺
                            ( positive-rational-ℕ⁺ (n⁺ *ℕ⁺ two-ℕ⁺))
                            ( positive-rational-ℕ⁺
                              ( succ-nonzero-ℕ' (n *ℕ 2 +ℕ k)))
                            ( preserves-leq-rational-ℕ
                              { n *ℕ 2}
                              { succ-ℕ (n *ℕ 2 +ℕ k)}
                              ( transitive-leq-ℕ _ _ _
                                ( succ-leq-ℕ (n *ℕ 2 +ℕ k))
                                ( leq-add-ℕ (n *ℕ 2) k))))))
                ≤ ( real-ℚ
                    ( ( rational-ℕ n) *ℚ
                      ( ( reciprocal-rational-ℕ⁺ n⁺) *ℚ
                        ( reciprocal-rational-ℕ⁺ two-ℕ⁺)))) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( λ q → real-ℚ (rational-ℕ n *ℚ q))
                          ( distributive-reciprocal-mul-ℕ⁺ n⁺ two-ℕ⁺))
                        ( refl))
                ≤ ( real-ℚ (reciprocal-rational-ℕ⁺ two-ℕ⁺)) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( real-ℚ)
                          ( is-section-left-div-ℚ⁺ (positive-rational-ℕ⁺ n⁺) _))
                        ( refl))
                ≤ ( raise-real-ℚ l (reciprocal-rational-ℕ⁺ two-ℕ⁺)) *ℝ
                  ( abs-ℝ
                    ( term-at-point-exp-power-series-at-zero-ℝ x (n *ℕ 2 +ℕ k)))
                  by
                    leq-sim-ℝ
                      ( preserves-sim-right-mul-ℝ _ _ _ (sim-raise-ℝ l _)))))
```

### The convergent power series of the exponential function

```agda
exp-convergent-everywhere-power-series-at-zero-ℝ :
  (l : Level) → convergent-everywhere-power-series-at-zero-ℝ l
exp-convergent-everywhere-power-series-at-zero-ℝ l =
  ( exp-power-series-at-zero-ℝ l ,
    is-convergent-everywhere-exp-power-series-at-zero-ℝ l)
```
