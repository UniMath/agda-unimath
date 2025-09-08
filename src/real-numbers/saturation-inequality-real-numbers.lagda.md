# Saturation of inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.saturation-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

If `x ≤ y + ε` for [real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` and every
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
then `x ≤ y`.

Despite being a property of
[inequality of real numbers](real-numbers.inequality-real-numbers.md), this is
much easier to prove via
[strict inequality](real-numbers.strict-inequality-real-numbers.md), so it is
moved to its own file to prevent circular dependency.

## Proof

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    saturated-leq-ℝ : ((ε : ℚ⁺) → leq-ℝ x (y +ℝ real-ℚ⁺ ε)) → leq-ℝ x y
    saturated-leq-ℝ H =
      saturated-le-ℝ x y
        ( λ ε →
          concatenate-leq-le-ℝ
            ( x)
            ( y +ℝ real-ℚ⁺ (mediant-zero-ℚ⁺ ε))
            ( y +ℝ real-ℚ⁺ ε)
            ( H (mediant-zero-ℚ⁺ ε))
            ( preserves-le-left-add-ℝ
              ( y)
              ( real-ℚ⁺ (mediant-zero-ℚ⁺ ε))
              ( real-ℚ⁺ ε)
              ( preserves-le-real-ℚ _ _ (le-mediant-zero-ℚ⁺ ε))))
```
