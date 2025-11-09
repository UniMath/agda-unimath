# Multiplication by positive, negative, and nonnegative real numbers

```agda
module real-numbers.multiplication-positive-and-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

When we have information about the sign of the factors of a
[product](real-numbers.multiplication-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md), we can deduce the sign of
their product too.

## Lemmas

### The product of a positive and a negative rational number is negative

```agda
abstract
  is-negative-mul-positive-negative-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-positive-ℝ x → is-negative-ℝ y →
    is-negative-ℝ (x *ℝ y)
  is-negative-mul-positive-negative-ℝ {x = x} {y = y} is-pos-x is-neg-y =
    preserves-le-right-sim-ℝ
      ( x *ℝ y)
      ( x *ℝ zero-ℝ)
      ( zero-ℝ)
      ( right-zero-law-mul-ℝ x)
      ( preserves-le-left-mul-ℝ⁺ (x , is-pos-x) is-neg-y)

mul-positive-negative-ℝ :
  {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁻ l2 → ℝ⁻ (l1 ⊔ l2)
mul-positive-negative-ℝ (x , is-pos-x) (y , is-neg-y) =
  ( x *ℝ y , is-negative-mul-positive-negative-ℝ is-pos-x is-neg-y)
```
