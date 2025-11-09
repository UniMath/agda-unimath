# Inequalities about addition and subtraction on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequalities-addition-and-subtraction-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

This file describes lemmas about
[inequalities](real-numbers.inequality-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) related to
[addition](real-numbers.addition-real-numbers.md) and
[subtraction](real-numbers.difference-real-numbers.md).

## Lemmas

### Inequality on the real numbers is translation invariant

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract opaque
    unfolding add-ℝ leq-ℝ

    preserves-leq-right-add-ℝ : leq-ℝ x y → leq-ℝ (x +ℝ z) (y +ℝ z)
    preserves-leq-right-add-ℝ x≤y _ =
      map-tot-exists (λ (qx , _) → map-product (x≤y qx) id)

    preserves-leq-left-add-ℝ : leq-ℝ x y → leq-ℝ (z +ℝ x) (z +ℝ y)
    preserves-leq-left-add-ℝ x≤y _ =
      map-tot-exists (λ (_ , qx) → map-product id (map-product (x≤y qx) id))

abstract
  preserves-leq-diff-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    leq-ℝ x y → leq-ℝ (x -ℝ z) (y -ℝ z)
  preserves-leq-diff-ℝ z = preserves-leq-right-add-ℝ (neg-ℝ z)

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    reflects-leq-right-add-ℝ : leq-ℝ (x +ℝ z) (y +ℝ z) → leq-ℝ x y
    reflects-leq-right-add-ℝ x+z≤y+z =
      preserves-leq-sim-ℝ
        ( cancel-right-add-diff-ℝ x z)
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-leq-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z≤y+z)

    reflects-leq-left-add-ℝ : leq-ℝ (z +ℝ x) (z +ℝ y) → leq-ℝ x y
    reflects-leq-left-add-ℝ z+x≤z+y =
      reflects-leq-right-add-ℝ
        ( binary-tr
          ( leq-ℝ)
          ( commutative-add-ℝ z x)
          ( commutative-add-ℝ z y)
          ( z+x≤z+y))

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-translate-right-leq-ℝ : leq-ℝ x y ↔ leq-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-translate-right-leq-ℝ = preserves-leq-right-add-ℝ z x y
  pr2 iff-translate-right-leq-ℝ = reflects-leq-right-add-ℝ z x y

  iff-translate-left-leq-ℝ : leq-ℝ x y ↔ leq-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-translate-left-leq-ℝ = preserves-leq-left-add-ℝ z x y
  pr2 iff-translate-left-leq-ℝ = reflects-leq-left-add-ℝ z x y

abstract
  preserves-leq-add-ℝ :
    {l1 l2 l3 l4 : Level} {a : ℝ l1} {b : ℝ l2} {c : ℝ l3} {d : ℝ l4} →
    leq-ℝ a b → leq-ℝ c d → leq-ℝ (a +ℝ c) (b +ℝ d)
  preserves-leq-add-ℝ {a = a} {b = b} {c = c} {d = d} a≤b c≤d =
    transitive-leq-ℝ
      ( a +ℝ c)
      ( a +ℝ d)
      ( b +ℝ d)
      ( preserves-leq-right-add-ℝ d a b a≤b)
      ( preserves-leq-left-add-ℝ a c d c≤d)
```

### Transposition laws

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    leq-transpose-left-diff-ℝ : leq-ℝ (x -ℝ y) z → leq-ℝ x (z +ℝ y)
    leq-transpose-left-diff-ℝ x-y≤z =
      preserves-leq-left-sim-ℝ
        ( cancel-right-diff-add-ℝ x y)
        ( preserves-leq-right-add-ℝ y (x -ℝ y) z x-y≤z)

    leq-transpose-left-add-ℝ : leq-ℝ (x +ℝ y) z → leq-ℝ x (z -ℝ y)
    leq-transpose-left-add-ℝ x+y≤z =
      preserves-leq-left-sim-ℝ
        ( cancel-right-add-diff-ℝ x y)
        ( preserves-leq-right-add-ℝ (neg-ℝ y) (x +ℝ y) z x+y≤z)

    leq-transpose-right-add-ℝ : leq-ℝ x (y +ℝ z) → leq-ℝ (x -ℝ z) y
    leq-transpose-right-add-ℝ x≤y+z =
      preserves-leq-right-sim-ℝ
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-leq-right-add-ℝ (neg-ℝ z) x (y +ℝ z) x≤y+z)

    leq-transpose-right-diff-ℝ : leq-ℝ x (y -ℝ z) → leq-ℝ (x +ℝ z) y
    leq-transpose-right-diff-ℝ x≤y-z =
      preserves-leq-right-sim-ℝ
        ( cancel-right-diff-add-ℝ y z)
        ( preserves-leq-right-add-ℝ z x (y -ℝ z) x≤y-z)
```

### Swapping laws

```agda
abstract
  swap-right-diff-leq-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (x -ℝ y) z → leq-ℝ (x -ℝ z) y
  swap-right-diff-leq-ℝ x y z x-y≤z =
    leq-transpose-right-add-ℝ
      ( x)
      ( y)
      ( z)
      ( tr
        ( leq-ℝ x)
        ( commutative-add-ℝ _ _)
        ( leq-transpose-left-diff-ℝ x y z x-y≤z))
```

### Addition of real numbers preserves lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    preserves-lower-neighborhood-leq-left-add-ℝ :
      leq-ℝ y (z +ℝ real-ℚ⁺ d) →
      leq-ℝ (x +ℝ y) ((x +ℝ z) +ℝ real-ℚ⁺ d)
    preserves-lower-neighborhood-leq-left-add-ℝ z≤y+d =
      inv-tr
        ( leq-ℝ (x +ℝ y))
        ( associative-add-ℝ x z (real-ℚ⁺ d))
        ( preserves-leq-left-add-ℝ
          ( x)
          ( y)
          ( z +ℝ real-ℚ⁺ d)
          ( z≤y+d))

    preserves-lower-neighborhood-leq-right-add-ℝ :
      leq-ℝ y (z +ℝ real-ℚ⁺ d) →
      leq-ℝ (y +ℝ x) ((z +ℝ x) +ℝ real-ℚ⁺ d)
    preserves-lower-neighborhood-leq-right-add-ℝ z≤y+d =
      binary-tr
        ( λ u v → leq-ℝ u (v +ℝ real-ℚ⁺ d))
        ( commutative-add-ℝ x y)
        ( commutative-add-ℝ x z)
        ( preserves-lower-neighborhood-leq-left-add-ℝ z≤y+d)
```

### Addition of real numbers reflects lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    reflects-lower-neighborhood-leq-left-add-ℝ :
      leq-ℝ (x +ℝ y) ((x +ℝ z) +ℝ real-ℚ⁺ d) →
      leq-ℝ y (z +ℝ real-ℚ⁺ d)
    reflects-lower-neighborhood-leq-left-add-ℝ x+y≤x+z+d =
      reflects-leq-left-add-ℝ
        ( x)
        ( y)
        ( z +ℝ real-ℚ⁺ d)
        ( tr
          ( leq-ℝ (x +ℝ y))
          ( associative-add-ℝ x z (real-ℚ⁺ d))
          ( x+y≤x+z+d))

    reflects-lower-neighborhood-leq-right-add-ℝ :
      leq-ℝ (y +ℝ x) ((z +ℝ x) +ℝ real-ℚ⁺ d) →
      leq-ℝ y (z +ℝ real-ℚ⁺ d)
    reflects-lower-neighborhood-leq-right-add-ℝ y+x≤z+y+d =
      reflects-lower-neighborhood-leq-left-add-ℝ
        ( binary-tr
          ( λ u v → leq-ℝ u (v +ℝ real-ℚ⁺ d))
          ( commutative-add-ℝ y x)
          ( commutative-add-ℝ z x)
          ( y+x≤z+y+d))
```
