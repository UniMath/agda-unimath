# Inequality of arithmetic and geometric means on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.inequality-arithmetic-geometric-means-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import foundation.identity-types
open import elementary-number-theory.nonnegative-rational-numbers
open import foundation.transport-along-identifications
open import foundation.action-on-identifications-functions
open import elementary-number-theory.additive-group-of-rational-numbers
```

</details>

## Idea

Though we cannot e.g. take square roots on the rational numbers to compute
geometric means, we can still prove the inequality that `4xy ≤ (x + y)²`.

```agda
abstract
  leq-gm-am-ℚ :
    (x y : ℚ) →
    leq-ℚ (rational-ℕ 4 *ℚ (x *ℚ y)) (square-ℚ (x +ℚ y))
  leq-gm-am-ℚ x y =
    leq-is-nonnegative-diff-ℚ
      ( rational-ℕ 4 *ℚ (x *ℚ y))
      ( square-ℚ (x +ℚ y))
      ( inv-tr
        ( is-nonnegative-ℚ)
        ( equational-reasoning
          square-ℚ (x +ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y)
          ＝
            ((square-ℚ x +ℚ rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y) -ℚ
            rational-ℕ 4 *ℚ (x *ℚ y)
            by
              ap
                ( _-ℚ rational-ℕ 4 *ℚ (x *ℚ y))
                ( square-add-ℚ x y)
          ＝
            ((square-ℚ x +ℚ square-ℚ y) +ℚ
            rational-ℕ 2 *ℚ (x *ℚ y)) -ℚ
            rational-ℕ 4 *ℚ (x *ℚ y)
            by
              ap
                ( _-ℚ rational-ℕ 4 *ℚ (x *ℚ y))
                ( right-swap-add-ℚ
                  ( square-ℚ x)
                  ( rational-ℕ 2 *ℚ (x *ℚ y))
                  ( square-ℚ y))
          ＝
            (square-ℚ x +ℚ square-ℚ y) +ℚ
            (rational-ℕ 2 *ℚ (x *ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y))
            by
              associative-add-ℚ
                ( square-ℚ x +ℚ square-ℚ y)
                ( rational-ℕ 2 *ℚ (x *ℚ y))
                ( neg-ℚ (rational-ℕ 4 *ℚ (x *ℚ y)))
          ＝
            (square-ℚ x +ℚ square-ℚ y) +ℚ
            ((rational-ℕ 2 -ℚ rational-ℕ 4) *ℚ (x *ℚ y))
            by
              ap
                ( square-ℚ x +ℚ square-ℚ y +ℚ_)
                ( inv (right-distributive-mul-diff-ℚ _ _ _))
          ＝
            (square-ℚ x +ℚ square-ℚ y) +ℚ
            (rational-ℤ (neg-ℤ (int-ℕ 2)) *ℚ (x *ℚ y))
            by
              ap
                ( square-ℚ x +ℚ square-ℚ y +ℚ_)
                ( ap
                  ( _*ℚ (x *ℚ y))
                  (diff-rational-ℤ _ _))
          ＝
            (square-ℚ x +ℚ square-ℚ y) -ℚ
            (rational-ℕ 2 *ℚ (x *ℚ y))
            by
              ap
                ( square-ℚ x +ℚ square-ℚ y +ℚ_)
                ( left-negative-law-mul-ℚ _ _)
          ＝ square-ℚ x -ℚ (rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
            by
              right-swap-add-ℚ
                ( square-ℚ x)
                ( square-ℚ y)
                ( neg-ℚ (rational-ℕ 2 *ℚ (x *ℚ y)))
          ＝ square-ℚ (x -ℚ y) by inv (square-diff-ℚ x y))
        ( is-nonnegative-square-ℚ (x -ℚ y)))
```
