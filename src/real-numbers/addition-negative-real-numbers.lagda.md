# Addition of negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.negative-real-numbers
open import real-numbers.dedekind-real-numbers
open import foundation.transport-along-identifications
open import real-numbers.rational-real-numbers
open import real-numbers.negation-real-numbers
open import foundation.functoriality-disjunction
open import real-numbers.addition-positive-real-numbers
open import foundation.disjunction
open import real-numbers.addition-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import foundation.universe-levels
open import foundation.dependent-pair-types
```

</details>

## Idea

The [negative](real-numbers.negative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are closed under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
abstract
  is-negative-add-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-negative-ℝ x → is-negative-ℝ y →
    is-negative-ℝ (x +ℝ y)
  is-negative-add-ℝ {x = x} {y = y} x<0 y<0 =
    transitive-le-ℝ
      ( x +ℝ y)
      ( x)
      ( zero-ℝ)
      ( x<0)
      ( tr
        ( le-ℝ (x +ℝ y))
        ( right-unit-law-add-ℝ x)
        ( preserves-le-left-add-ℝ x y zero-ℝ y<0))

add-ℝ⁻ : {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁻ l2 → ℝ⁻ (l1 ⊔ l2)
add-ℝ⁻ (x , x<0) (y , y<0) = (add-ℝ x y , is-negative-add-ℝ x<0 y<0)

infixl 35 _+ℝ⁻_

_+ℝ⁻_ : {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁻ l2 → ℝ⁻ (l1 ⊔ l2)
_+ℝ⁻_ = add-ℝ⁻
```

## Properties

### If `x + y` is negative, `x` or `y` is negative

```agda
abstract
  is-negative-either-is-negative-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-negative-ℝ (x +ℝ y) →
    disjunction-type (is-negative-ℝ x) (is-negative-ℝ y)
  is-negative-either-is-negative-add-ℝ x y x+y<0 =
    map-disjunction
      ( is-negative-is-positive-neg-ℝ x)
      ( is-negative-is-positive-neg-ℝ y)
      ( is-positive-either-is-positive-add-ℝ
        ( neg-ℝ x)
        ( neg-ℝ y)
        ( tr
          ( is-positive-ℝ)
          ( distributive-neg-add-ℝ x y)
          ( neg-is-negative-ℝ (x +ℝ y) x+y<0)))
```
