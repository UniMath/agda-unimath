# The addition isometry on rational numbers

```agda
module elementary-number-theory.isometry-addition-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.isometries-metric-spaces
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import foundation.transport-along-identifications
open import elementary-number-theory.positive-rational-numbers
open import foundation.dependent-pair-types
open import elementary-number-theory.rational-numbers
```

</details>

## Idea

For any [rational number](elementary-number-theory.rational-numbers.md) `q`,
[addition](elementary-number-theory.addition-rational-numbers.md) of `q` is an
[isometry](metric-spaces.isometries-metric-spaces.md) from the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md)
to itself.

## Definitions

```agda
module _
  (q : ℚ)
  where

  abstract
    is-isometry-left-add-ℚ :
      is-isometry-Metric-Space metric-space-ℚ metric-space-ℚ (add-ℚ q)
    pr1 (is-isometry-left-add-ℚ d x y) (y≤x+d , x≤y+d) =
      ( inv-tr
          ( leq-ℚ (q +ℚ y))
          ( associative-add-ℚ _ _ _)
          ( preserves-leq-right-add-ℚ q y (x +ℚ rational-ℚ⁺ d) y≤x+d) ,
        inv-tr
          ( leq-ℚ (q +ℚ x))
          ( associative-add-ℚ _ _ _)
          ( preserves-leq-right-add-ℚ q x (y +ℚ rational-ℚ⁺ d) x≤y+d))
    pr2 (is-isometry-left-add-ℚ d x y) (q+y≤q+x+d , q+x≤q+y+d) =
      ( reflects-leq-right-add-ℚ
          ( q)
          ( y)
          ( x +ℚ rational-ℚ⁺ d)
          ( tr (leq-ℚ (q +ℚ y)) (associative-add-ℚ _ _ _) q+y≤q+x+d) ,
        reflects-leq-right-add-ℚ
          ( q)
          ( x)
          ( y +ℚ rational-ℚ⁺ d)
          ( tr (leq-ℚ (q +ℚ x)) (associative-add-ℚ _ _ _) q+x≤q+y+d))

  isometry-left-add-ℚ : isometry-Metric-Space metric-space-ℚ metric-space-ℚ
  isometry-left-add-ℚ = (add-ℚ q , is-isometry-left-add-ℚ)
```
