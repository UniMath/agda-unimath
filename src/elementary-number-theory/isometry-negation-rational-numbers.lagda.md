# The negation isometry on rational numbers

```agda
module elementary-number-theory.isometry-negation-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.isometries-metric-spaces
open import elementary-number-theory.inequality-rational-numbers
open import foundation.identity-types
open import elementary-number-theory.addition-rational-numbers
open import foundation.binary-transport
open import foundation.transport-along-identifications
open import elementary-number-theory.positive-rational-numbers
open import foundation.dependent-pair-types
open import elementary-number-theory.rational-numbers
```

</details>

## Idea

Negation is an [isometry](metric-spaces.isometries-metric-spaces.md) from the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md)
to itself.

## Definition

```agda
abstract
  is-isometry-neg-ℚ :
    is-isometry-Metric-Space metric-space-ℚ metric-space-ℚ neg-ℚ
  pr1 (is-isometry-neg-ℚ d x y) (y≤x+d , x≤y+d) =
    ( leq-transpose-left-diff-ℚ
        ( neg-ℚ y)
        ( rational-ℚ⁺ d)
        ( neg-ℚ x)
        ( tr (_≤-ℚ neg-ℚ x) (distributive-neg-add-ℚ _ _) (neg-leq-ℚ x≤y+d)) ,
      leq-transpose-left-diff-ℚ
        ( neg-ℚ x)
        ( rational-ℚ⁺ d)
        ( neg-ℚ y)
        ( tr (_≤-ℚ neg-ℚ y) (distributive-neg-add-ℚ _ _) (neg-leq-ℚ y≤x+d)))
  pr2 (is-isometry-neg-ℚ d x y) (-y≤-x+d , -x≤-y+d) =
    ( leq-transpose-left-diff-ℚ
        ( y)
        ( rational-ℚ⁺ d)
        ( x)
        ( binary-tr
          ( leq-ℚ)
          ( distributive-neg-add-ℚ _ _ ∙ ap-add-ℚ (neg-neg-ℚ y) refl)
          ( neg-neg-ℚ x)
          ( neg-leq-ℚ -x≤-y+d)) ,
      leq-transpose-left-diff-ℚ
        ( x)
        ( rational-ℚ⁺ d)
        ( y)
        ( binary-tr
          ( leq-ℚ)
          ( distributive-neg-add-ℚ _ _ ∙ ap-add-ℚ (neg-neg-ℚ x) refl)
          ( neg-neg-ℚ y)
          ( neg-leq-ℚ -y≤-x+d)))

  isometry-neg-ℚ : isometry-Metric-Space metric-space-ℚ metric-space-ℚ
  isometry-neg-ℚ = (neg-ℚ , is-isometry-neg-ℚ)
```
