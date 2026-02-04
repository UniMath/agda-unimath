# Addition of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are closed under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
abstract
  is-positive-add-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-positive-ℝ x → is-positive-ℝ y →
    is-positive-ℝ (x +ℝ y)
  is-positive-add-ℝ {x = x} {y = y} 0<x 0<y =
    transitive-le-ℝ
      ( zero-ℝ)
      ( x)
      ( x +ℝ y)
      ( tr
        ( λ z → le-ℝ z (x +ℝ y))
        ( right-unit-law-add-ℝ x)
        ( preserves-le-left-add-ℝ x zero-ℝ y 0<y))
      ( 0<x)

add-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
add-ℝ⁺ (x , is-pos-x) (y , is-pos-y) =
  ( x +ℝ y , is-positive-add-ℝ is-pos-x is-pos-y)

infixl 35 _+ℝ⁺_

_+ℝ⁺_ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
_+ℝ⁺_ = add-ℝ⁺
```

### Addition with a positive real number is a strictly inflationary map

```agda
abstract opaque
  unfolding add-ℝ le-ℝ

  le-left-add-real-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ x (x +ℝ real-ℝ⁺ d)
  le-left-add-real-ℝ⁺ x d⁺@(d , pos-d) =
    tr
      ( λ y → le-ℝ y (x +ℝ d))
      ( right-unit-law-add-ℝ x)
      ( preserves-le-left-add-ℝ x zero-ℝ d pos-d)

  le-left-add-real-ℚ⁺ :
    {l : Level} (x : ℝ l) (d : ℚ⁺) → le-ℝ x (x +ℝ real-ℚ⁺ d)
  le-left-add-real-ℚ⁺ x d =
    le-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ d)

abstract
  le-right-add-real-ℝ⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ x (real-ℝ⁺ d +ℝ x)
  le-right-add-real-ℝ⁺ x d =
    tr (le-ℝ x) (commutative-add-ℝ x (real-ℝ⁺ d)) (le-left-add-real-ℝ⁺ x d)

  leq-left-add-real-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ l1) (d : ℝ⁺ l2) → leq-ℝ x (x +ℝ real-ℝ⁺ d)
  leq-left-add-real-ℝ⁺ x d = leq-le-ℝ (le-left-add-real-ℝ⁺ x d)

  leq-right-add-real-ℝ⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → leq-ℝ x (real-ℝ⁺ d +ℝ x)
  leq-right-add-real-ℝ⁺ x d = leq-le-ℝ (le-right-add-real-ℝ⁺ x d)

  leq-left-add-real-ℚ⁺ :
    {l : Level} (x : ℝ l) (d : ℚ⁺) → leq-ℝ x (x +ℝ real-ℚ⁺ d)
  leq-left-add-real-ℚ⁺ x d = leq-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ d)
```

### Subtraction by a positive real number is a strictly deflationary map

```agda
abstract
  le-diff-real-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ (x -ℝ real-ℝ⁺ d) x
  le-diff-real-ℝ⁺ x d⁺@(d , _) =
    preserves-le-right-sim-ℝ
      ( x -ℝ d)
      ( (x -ℝ d) +ℝ d)
      ( x)
      ( tr
        ( λ y → sim-ℝ y x)
        ( right-swap-add-ℝ x d (neg-ℝ d))
        ( cancel-right-add-diff-ℝ x d))
      ( le-left-add-real-ℝ⁺ (x -ℝ d) d⁺)

  leq-diff-real-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ l1) (d : ℝ⁺ l2) → leq-ℝ (x -ℝ real-ℝ⁺ d) x
  leq-diff-real-ℝ⁺ x d = leq-le-ℝ (le-diff-real-ℝ⁺ x d)

  le-diff-real-ℚ⁺ :
    {l : Level} (x : ℝ l) (d : ℚ⁺) → le-ℝ (x -ℝ real-ℚ⁺ d) x
  le-diff-real-ℚ⁺ x d = le-diff-real-ℝ⁺ x (positive-real-ℚ⁺ d)

  leq-diff-real-ℚ⁺ :
    {l : Level} (x : ℝ l) (d : ℚ⁺) → leq-ℝ (x -ℝ real-ℚ⁺ d) x
  leq-diff-real-ℚ⁺ x d = leq-le-ℝ (le-diff-real-ℚ⁺ x d)
```

### If the sum of two real numbers is positive, one of them is positive

```agda
abstract opaque
  unfolding add-ℝ

  is-positive-either-is-positive-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-positive-ℝ (x +ℝ y) →
    disjunction-type (is-positive-ℝ x) (is-positive-ℝ y)
  is-positive-either-is-positive-add-ℝ x y 0<x+y =
    let
      open do-syntax-trunc-Prop (is-positive-prop-ℝ x ∨ is-positive-prop-ℝ y)
    in do
      ((p , q) , p<x , q<y , 0=p+q) ← zero-in-lower-cut-ℝ⁺ (x +ℝ y , 0<x+y)
      rec-coproduct
        ( λ is-neg-p →
          inr-disjunction
            ( is-positive-exists-ℚ⁺-in-lower-cut-ℝ
              ( y)
              ( intro-exists
                ( neg-ℚ⁻ (p , is-neg-p))
                ( tr
                  ( is-in-lower-cut-ℝ y)
                  ( unique-right-neg-ℚ p q (inv 0=p+q))
                  ( q<y)))))
        ( λ is-nonneg-p →
          inl-disjunction
            ( is-positive-zero-in-lower-cut-ℝ
              ( x)
              ( leq-lower-cut-ℝ x (leq-zero-is-nonnegative-ℚ is-nonneg-p) p<x)))
        ( decide-is-negative-is-nonnegative-ℚ p)
```
