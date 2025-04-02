# The maximum function on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
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
open import real-numbers.maxima-minima-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.minimum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[The maximum function on the real numbers](real-numbers.maximum-real-numbers.md)
is a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
abstract
  modulus-of-continuity-max-ℝ : ℚ⁺ → ℚ⁺
  modulus-of-continuity-max-ℝ = id

  is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ :
    {l1 l2 : Level} →
    is-modulus-of-uniform-continuity-Metric-Space
      ( product-Metric-Space (metric-space-leq-ℝ l1) (metric-space-leq-ℝ l2))
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( ind-product max-ℝ)
      ( modulus-of-continuity-max-ℝ)
  is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ
    (a , b) ε⁺@(ε , _) (a' , b') (a~a' , b~b') =
      let
        εℝ : ℝ lzero
        εℝ = real-ℚ ε
      in
        neighborhood-abs-diff-bound-leq-ℝ
          ( ε⁺)
          ( max-ℝ a b)
          ( max-ℝ a' b')
          ( leq-abs-leq-leq-neg-ℝ
            ( _)
            ( εℝ)
            ( inv-tr
              ( λ x → leq-ℝ x εℝ)
              ( diff-max-max-ℝ _ _ _ _)
              ( leq-max-leq-ℝ _ _
                ( εℝ)
                ( transitive-leq-ℝ
                  ( min-ℝ (a -ℝ a') (a -ℝ b'))
                  ( a -ℝ a')
                  ( εℝ)
                  ( diff-bound-neighborhood-leq-ℝ ε⁺ a a' a~a')
                  ( leq-left-min-ℝ _ _))
                ( transitive-leq-ℝ
                  ( min-ℝ (b -ℝ a') (b -ℝ b'))
                  ( b -ℝ b')
                  ( εℝ)
                  ( diff-bound-neighborhood-leq-ℝ ε⁺ b b' b~b')
                  ( leq-right-min-ℝ _ _))))
            ( inv-tr
              ( λ x → leq-ℝ x εℝ)
              ( distributive-neg-diff-ℝ _ _ ∙ diff-max-max-ℝ _ _ _ _)
              ( leq-max-leq-ℝ
                ( min-ℝ (a' -ℝ a) (a' -ℝ b))
                ( min-ℝ (b' -ℝ a) (b' -ℝ b))
                ( εℝ)
                ( transitive-leq-ℝ
                  ( min-ℝ (a' -ℝ a) (a' -ℝ b))
                  ( a' -ℝ a)
                  ( εℝ)
                  ( reversed-diff-bound-neighborhood-leq-ℝ ε⁺ a a' a~a')
                  ( leq-left-min-ℝ _ _))
                ( transitive-leq-ℝ
                  ( min-ℝ (b' -ℝ a) (b' -ℝ b))
                  ( b' -ℝ b)
                  ( εℝ)
                  ( reversed-diff-bound-neighborhood-leq-ℝ ε⁺ b b' b~b')
                  ( leq-right-min-ℝ _ _)))))

  is-uniformly-continuous-max-ℝ :
    {l1 l2 : Level} →
    is-uniformly-continuous-binary-map-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( max-ℝ)
  is-uniformly-continuous-max-ℝ =
    intro-exists
      ( modulus-of-continuity-max-ℝ)
      ( is-modulus-of-uniform-continuity-modulus-of-continuity-max-ℝ)
```
