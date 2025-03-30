# Addition on the real numbers is uniformly continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import elementary-number-theory.positive-rational-numbers
open import foundation.cartesian-product-types
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import foundation.function-types
open import real-numbers.metric-space-of-real-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
open import metric-spaces.uniformly-continuous-binary-functions-metric-spaces
open import metric-spaces.products-metric-spaces
```

</details>

## Idea

[Addition on the real numbers](real-numbers.addition-real-numbers.md) is
a
[uniformly continuous binary function](metric-spaces.uniformly-continuous-binary-functions-metric-spaces.md)

## Proof

```agda
modulus-of-continuity-add-ℝ : ℚ⁺ → ℚ⁺
modulus-of-continuity-add-ℝ = pr1 ∘ bound-double-le-ℚ⁺

module _
  {l1 l2 : Level}
  where

  is-modulus-of-uniform-continuity-modulus-of-continuity-add-ℝ :
    is-modulus-of-uniform-continuity-Metric-Space
      ( product-Metric-Space (metric-space-leq-ℝ l1) (metric-space-leq-ℝ l2))
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( ind-product add-ℝ)
      ( modulus-of-continuity-add-ℝ)
  is-modulus-of-uniform-continuity-modulus-of-continuity-add-ℝ
    (a , b) ε (a' , b') (a~a' , b~b') =
      {!  a~a' !} , {!   !}
```
