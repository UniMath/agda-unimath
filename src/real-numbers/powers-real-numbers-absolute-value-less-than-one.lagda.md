# Powers of real numbers with absolute value less than one

```agda
module real-numbers.powers-real-numbers-absolute-value-less-than-one where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

If `|r| < 1`, then `rⁿ`
[approaches zero](real-numbers.real-sequences-approximating-zero.md) as `n`
grows. This fact is in its own file to avoid circular dependencies.

## Proof

```agda
abstract
  is-zero-lim-power-le-one-abs-ℝ :
    {l : Level} (r : ℝ l) → le-ℝ (abs-ℝ r) one-ℝ →
    is-zero-limit-sequence-ℝ (λ n → power-ℝ n r)
  is-zero-lim-power-le-one-abs-ℝ r |r|<1 =
    let
      open
        do-syntax-trunc-Prop (is-zero-limit-prop-sequence-ℝ (λ n → power-ℝ n r))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in do
      (ε , |r|<ε , ε<1ℝ) ← dense-rational-le-ℝ _ _ |r|<1
      let
        is-pos-ε =
          reflects-is-positive-real-ℚ
            ( is-positive-le-ℝ⁰⁺ (nonnegative-abs-ℝ r) (real-ℚ ε) |r|<ε)
        ε⁺ = (ε , is-pos-ε)
      is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ
        ( λ n → power-ℝ n r)
        ( (λ n → rational-ℚ⁺ (power-ℚ⁺ n ε⁺)) ,
          is-zero-limit-power-le-one-ℚ⁺ ε⁺ (reflects-le-real-ℚ ε<1ℝ))
        ( λ n →
          chain-of-inequalities
            abs-ℝ (power-ℝ n r)
            ≤ abs-ℝ (power-ℝ n (real-ℚ ε))
              by
                preserves-leq-abs-power-ℝ
                  ( n)
                  ( r)
                  ( real-ℚ ε)
                  ( inv-tr
                    ( leq-ℝ (abs-ℝ r))
                    ( abs-real-ℝ⁺ (positive-real-ℚ⁺ ε⁺))
                    ( leq-le-ℝ |r|<ε))
            ≤ power-ℝ n (real-ℚ ε)
              by
                leq-eq-ℝ
                  ( abs-real-ℝ⁺
                    ( power-ℝ n (real-ℚ ε) ,
                      is-positive-power-real-ℝ⁺ n (positive-real-ℚ⁺ ε⁺)))
            ≤ real-ℚ (power-ℚ n ε)
              by leq-eq-ℝ (power-real-ℚ n ε)
            ≤ real-ℚ⁺ (power-ℚ⁺ n ε⁺)
              by leq-eq-ℝ (ap real-ℚ (power-rational-ℚ⁺ n ε⁺)))
```
