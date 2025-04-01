# Addition on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.products-metric-spaces
open import metric-spaces.uniformly-continuous-binary-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[Addition on the real numbers](real-numbers.addition-real-numbers.md) is a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
modulus-of-continuity-add-ℝ : ℚ⁺ → ℚ⁺
modulus-of-continuity-add-ℝ = pr1 ∘ bound-double-le-ℚ⁺

module _
  {l1 l2 : Level}
  where

  abstract
    is-modulus-of-uniform-continuity-modulus-of-continuity-add-ℝ :
      is-modulus-of-uniform-continuity-Metric-Space
        ( product-Metric-Space (metric-space-leq-ℝ l1) (metric-space-leq-ℝ l2))
        ( metric-space-leq-ℝ (l1 ⊔ l2))
        ( ind-product add-ℝ)
        ( modulus-of-continuity-add-ℝ)
    is-modulus-of-uniform-continuity-modulus-of-continuity-add-ℝ
      (a , b) ε⁺@(ε , _) (a' , b') (a~a' , b~b') =
        let
          (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        in
          neighborhood-abs-diff-bound-leq-ℝ
            ( ε⁺)
            ( a +ℝ b)
            ( a' +ℝ b')
            ( inv-tr
              ( λ z → leq-ℝ z (real-ℚ ε))
              ( ap abs-ℝ (interchange-law-diff-add-ℝ a b a' b'))
              ( transitive-leq-ℝ
                ( abs-ℝ ((a -ℝ a') +ℝ (b -ℝ b')))
                ( abs-ℝ (a -ℝ a') +ℝ abs-ℝ (b -ℝ b'))
                ( real-ℚ ε)
                ( transitive-leq-ℝ
                  ( abs-ℝ (a -ℝ a') +ℝ abs-ℝ (b -ℝ b'))
                  ( real-ℚ ε' +ℝ real-ℚ ε')
                  ( real-ℚ ε)
                  ( inv-tr
                    ( λ p → leq-ℝ p (real-ℚ ε))
                    ( add-real-ℚ ε' ε')
                    ( preserves-leq-real-ℚ _ _ (leq-le-ℚ {ε' +ℚ ε'} {ε} 2ε'<ε)))
                  ( preserves-leq-add-ℝ _ _ _ _
                    ( abs-diff-bound-neighborhood-leq-ℝ ε'⁺ a a' a~a')
                    ( abs-diff-bound-neighborhood-leq-ℝ ε'⁺ b b' b~b')))
                ( triangle-inequality-abs-ℝ _ _)))

    is-uniformly-continuous-add-ℝ :
      is-uniformly-continuous-binary-map-Metric-Space
        ( metric-space-leq-ℝ l1)
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2))
        ( add-ℝ)
    is-uniformly-continuous-add-ℝ =
      intro-exists
        ( modulus-of-continuity-add-ℝ)
        ( is-modulus-of-uniform-continuity-modulus-of-continuity-add-ℝ)
```
