# Saturation of inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.saturation-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
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

### If `x < y + ε` for every positive rational `ε`, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    saturated-le-ℝ : ((ε : ℚ⁺) → le-ℝ x (y +ℝ real-ℚ⁺ ε)) → leq-ℝ x y
    saturated-le-ℝ H =
      leq-not-le-ℝ y x
        ( λ y<x →
          let open do-syntax-trunc-Prop empty-Prop
          in do
            (ε , y+ε<x) ←
              exists-positive-rational-separation-le-ℝ {x = y} {y = x} y<x
            irreflexive-le-ℝ
              ( x)
              ( transitive-le-ℝ x (y +ℝ real-ℚ⁺ ε) x y+ε<x (H ε)))
```

### If `x ≤ y + ε` for every positive rational `ε`, then `x ≤ y`

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
              ( preserves-le-real-ℚ (le-mediant-zero-ℚ⁺ ε))))
```
