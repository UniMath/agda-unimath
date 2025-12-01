# Odd roots of real numbers

```agda
module real-numbers.odd-roots-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-space-of-rational-numbers

open import order-theory.posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

For any [odd](elementary-number-theory.parity-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) `n`, the `n`th
{{#concept "root" Disambiguation="odd roots of real numbers" Agda=odd-root-ℝ}}
operation is a map from `ℝ` to `ℝ` that is the inverse operation to the `n`th
power.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x : ℝ l)
  where

  lower-cut-odd-root-ℝ : subtype l ℚ
  lower-cut-odd-root-ℝ q = lower-cut-ℝ x (power-ℚ n q)

  upper-cut-odd-root-ℝ : subtype l ℚ
  upper-cut-odd-root-ℝ q = upper-cut-ℝ x (power-ℚ n q)

  abstract
    is-inhabited-lower-cut-odd-root-ℝ :
      is-inhabited-subtype lower-cut-odd-root-ℝ
    is-inhabited-lower-cut-odd-root-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop lower-cut-odd-root-ℝ)
      in do
        (q , q<x) ← is-inhabited-lower-cut-ℝ x
        let (p , pⁿ<q) = unbounded-below-odd-power-ℚ n q odd-n
        intro-exists p (le-lower-cut-ℝ x pⁿ<q q<x)

    is-inhabited-upper-cut-odd-root-ℝ :
      is-inhabited-subtype upper-cut-odd-root-ℝ
    is-inhabited-upper-cut-odd-root-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-subtype-Prop upper-cut-odd-root-ℝ)
      in do
        (q , x<q) ← is-inhabited-upper-cut-ℝ x
        let (p , q<pⁿ) = unbounded-above-odd-power-ℚ n q odd-n
        intro-exists p (le-upper-cut-ℝ x q<pⁿ x<q)

    forward-implication-is-rounded-lower-cut-odd-root-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-odd-root-ℝ q →
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-odd-root-ℝ r)
    forward-implication-is-rounded-lower-cut-odd-root-ℝ q qⁿ<x =
      let
        open inequality-reasoning-Poset ℚ-Poset
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-odd-root-ℝ r))
      in do
        (p , qⁿ<p , p<x) ←
          forward-implication (is-rounded-lower-cut-ℝ x (power-ℚ n q)) qⁿ<x
        let
          ε = positive-diff-le-ℚ qⁿ<p
        (δ , H) ←
          is-classically-pointwise-continuous-pointwise-continuous-function-ℝ
            ( pointwise-continuous-power-ℝ lzero n)
            ( real-ℚ q)
            ( ε)
        intro-exists
          ( q +ℚ rational-ℚ⁺ δ)
          ( le-right-add-rational-ℚ⁺ q δ ,
            leq-lower-cut-ℝ
              ( x)
              ( chain-of-inequalities
                power-ℚ n (q +ℚ rational-ℚ⁺ δ)
                ≤ power-ℚ n q +ℚ rational-ℚ⁺ ε
                  by
                    reflects-leq-real-ℚ
                      ( binary-tr
                        ( leq-ℝ)
                        ( power-real-ℚ n _)
                        ( ( ap-add-ℝ (power-real-ℚ n q) refl) ∙
                          ( add-real-ℚ _ _))
                        ( right-leq-real-bound-neighborhood-ℝ ε _ _
                          ( H
                            ( real-ℚ (q +ℚ rational-ℚ⁺ δ))
                            ( forward-implication
                              ( is-isometry-metric-space-real-ℚ
                                ( δ)
                                ( q)
                                ( q +ℚ rational-ℚ⁺ δ))
                                ( neighborhood-add-ℚ q δ)))))
                ≤ p
                  by leq-eq-ℚ (is-identity-right-conjugation-add-ℚ _ _))
              ( p<x))

    forward-implication-is-rounded-upper-cut-odd-root-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-odd-root-ℝ q →
      exists ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-odd-root-ℝ r)
```
