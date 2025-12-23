# The binary mean of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.binary-mean-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  binary-mean-ℝ : ℝ (l1 ⊔ l2)
  binary-mean-ℝ = one-half-ℝ *ℝ (x +ℝ y)
```

## Properties

### The binary mean of `x` and `x` is `x`

```agda
abstract
  is-idempotent-binary-mean-ℝ :
    {l : Level} (x : ℝ l) → binary-mean-ℝ x x ＝ x
  is-idempotent-binary-mean-ℝ x =
    equational-reasoning
    one-half-ℝ *ℝ (x +ℝ x)
    ＝ real-inv-ℝ⁺ two-ℝ⁺ *ℝ (real-ℕ 2 *ℝ x)
      by
        ap-mul-ℝ
          ( ( inv
              ( real-inv-positive-real-ℚ⁺ (positive-rational-ℕ⁺ two-ℕ⁺)) ∙
            ( ap real-inv-ℝ⁺ (eq-ℝ⁺ _ _ (refl {x = real-ℕ 2})))))
          ( inv (left-mul-real-ℕ 2 x))
    ＝ x
      by eq-sim-ℝ (cancel-left-div-mul-ℝ⁺ two-ℝ⁺ x)
```

### If `z ≤ x` and `z ≤ y`, then `z ≤ binary-mean-ℝ x y`

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    leq-binary-mean-leq-both-ℝ :
      {l3 : Level} (z : ℝ l3) →
      leq-ℝ z x → leq-ℝ z y → leq-ℝ z (binary-mean-ℝ x y)
    leq-binary-mean-leq-both-ℝ z z≤x z≤y =
      tr
        ( λ w → leq-ℝ w (binary-mean-ℝ x y))
        ( is-idempotent-binary-mean-ℝ z)
        ( preserves-leq-left-mul-ℝ⁺ one-half-ℝ⁺ (preserves-leq-add-ℝ z≤x z≤y))
```

### If `x ≤ z` and `y ≤ z`, then `binary-mean-ℝ x y ≤ z`

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    geq-binary-mean-geq-both-ℝ :
      {l3 : Level} (z : ℝ l3) →
      leq-ℝ x z → leq-ℝ y z → leq-ℝ (binary-mean-ℝ x y) z
    geq-binary-mean-geq-both-ℝ z x≤z y≤z =
      tr
        ( leq-ℝ (binary-mean-ℝ x y))
        ( is-idempotent-binary-mean-ℝ z)
        ( preserves-leq-left-mul-ℝ⁺ one-half-ℝ⁺ (preserves-leq-add-ℝ x≤z y≤z))
```

### `y - binary-mean-ℝ x y = binary-mean-ℝ y (neg-ℝ x)`
