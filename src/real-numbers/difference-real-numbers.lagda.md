# The difference between real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.difference-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The {{#concept "difference" Disambiguation="real numbers" Agda=diff-ℝ}} of two
[real numbers](real-numbers.dedekind-real-numbers.md) `x` and `y` is the sum of
`x` and the [negation](real-numbers.negation-real-numbers.md) of `y`.

## Definition

```agda
diff-ℝ : {l1 l2 : Level} → (x : ℝ l1) → (y : ℝ l2) → ℝ (l1 ⊔ l2)
diff-ℝ x y = add-ℝ x (neg-ℝ y)

infixl 36 _-ℝ_
_-ℝ_ = diff-ℝ

ap-diff-ℝ :
  {l1 : Level} {x x' : ℝ l1} → (x ＝ x') →
  {l2 : Level} {y y' : ℝ l2} → (y ＝ y') →
  (x -ℝ y) ＝ (x' -ℝ y')
ap-diff-ℝ x=x' y=y' = ap-binary diff-ℝ x=x' y=y'
```

## Properties

### The inclusion of rational numbers preserves differences

```agda
abstract
  diff-real-ℚ : (p q : ℚ) → (real-ℚ p) -ℝ (real-ℚ q) ＝ real-ℚ (p -ℚ q)
  diff-real-ℚ p q = ap (real-ℚ p +ℝ_) (neg-real-ℚ q) ∙ add-real-ℚ p (neg-ℚ q)
```

### The negative of the difference of `x` and `y` is the difference of `y` and `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    distributive-neg-diff-ℝ : neg-ℝ (x -ℝ y) ＝ y -ℝ x
    distributive-neg-diff-ℝ =
      equational-reasoning
        neg-ℝ (x -ℝ y)
        ＝ neg-ℝ x +ℝ neg-ℝ (neg-ℝ y) by distributive-neg-add-ℝ _ _
        ＝ neg-ℝ x +ℝ y by ap (neg-ℝ x +ℝ_) (neg-neg-ℝ y)
        ＝ y -ℝ x by commutative-add-ℝ _ _
```

### Interchange laws for addition and difference on real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (a : ℝ l1) (b : ℝ l2) (c : ℝ l3) (d : ℝ l4)
  where

  abstract
    interchange-law-diff-add-ℝ :
      (a +ℝ b) -ℝ (c +ℝ d) ＝ (a -ℝ c) +ℝ (b -ℝ d)
    interchange-law-diff-add-ℝ =
      ( ap ((a +ℝ b) +ℝ_) (distributive-neg-add-ℝ c d)) ∙
      ( interchange-law-add-add-ℝ _ _ _ _)
```

### The right unit law of subtraction

```agda
abstract
  right-unit-law-diff-ℝ : {l : Level} (x : ℝ l) → x -ℝ zero-ℝ ＝ x
  right-unit-law-diff-ℝ x =
    ap-add-ℝ refl neg-zero-ℝ ∙ right-unit-law-add-ℝ x
```

### Subtraction preserves similarity on real numbers

```agda
abstract
  preserves-sim-diff-ℝ :
    {l1 l2 l3 l4 : Level} {a : ℝ l1} {a' : ℝ l2} {b : ℝ l3} {b' : ℝ l4} →
    sim-ℝ a a' → sim-ℝ b b' → sim-ℝ (a -ℝ b) (a' -ℝ b')
  preserves-sim-diff-ℝ a~a' b~b' =
    preserves-sim-add-ℝ a~a' (preserves-sim-neg-ℝ b~b')
```

### `(x - y) - z = x - (y + z)`

```agda
abstract
  associative-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    (x -ℝ y) -ℝ z ＝ x -ℝ (y +ℝ z)
  associative-diff-ℝ x y z =
    equational-reasoning
      (x -ℝ y) -ℝ z
      ＝ x +ℝ (neg-ℝ y -ℝ z)
        by associative-add-ℝ _ _ _
      ＝ x -ℝ (y +ℝ z)
        by ap-add-ℝ refl (inv (distributive-neg-add-ℝ y z))
```

### `(x - y) + (y - z) = x - z`

```agda
abstract
  add-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ ((x -ℝ y) +ℝ (y -ℝ z)) (x -ℝ z)
  add-diff-ℝ x y z =
    similarity-reasoning-ℝ
      (x -ℝ y) +ℝ (y -ℝ z)
      ~ℝ ((x -ℝ y) +ℝ y) -ℝ z
        by sim-eq-ℝ (inv (associative-add-ℝ _ _ _))
      ~ℝ x -ℝ z
        by preserves-sim-right-add-ℝ _ _ _ (cancel-right-diff-add-ℝ x y)
```

### `(x + z) - (y + z) = x - y`

```agda
abstract
  diff-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ ((x +ℝ z) -ℝ (y +ℝ z)) (x -ℝ y)
  diff-add-ℝ x y z =
    similarity-reasoning-ℝ
      (x +ℝ z) -ℝ (y +ℝ z)
      ~ℝ (x +ℝ z) +ℝ (neg-ℝ y -ℝ z)
        by sim-eq-ℝ (ap-add-ℝ refl (distributive-neg-add-ℝ y z))
      ~ℝ (x -ℝ y) +ℝ (z -ℝ z)
        by sim-eq-ℝ (interchange-law-add-add-ℝ _ _ _ _)
      ~ℝ (x -ℝ y) +ℝ zero-ℝ
        by preserves-sim-left-add-ℝ _ _ _ (right-inverse-law-add-ℝ z)
      ~ℝ x -ℝ y
        by sim-eq-ℝ (right-unit-law-add-ℝ (x -ℝ y))
```

### `(x - z) - (y - z) = x - y`

```agda
abstract
  diff-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ ((x -ℝ z) -ℝ (y -ℝ z)) (x -ℝ y)
  diff-diff-ℝ x y z = diff-add-ℝ x y (neg-ℝ z)
```

### `x - (x - y) = y`

```agda
abstract
  right-diff-diff-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x -ℝ (x -ℝ y)) y
  right-diff-diff-ℝ x y =
    similarity-reasoning-ℝ
      x -ℝ (x -ℝ y)
      ~ℝ x +ℝ (neg-ℝ x +ℝ neg-ℝ (neg-ℝ y))
        by sim-eq-ℝ (ap-add-ℝ refl (distributive-neg-add-ℝ _ _))
      ~ℝ neg-ℝ (neg-ℝ y)
        by cancel-left-add-diff-ℝ x _
      ~ℝ y
        by sim-eq-ℝ (neg-neg-ℝ y)
```

### `x + (y - x) = y`

```agda
abstract
  add-right-diff-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x +ℝ (y -ℝ x)) y
  add-right-diff-ℝ x y =
    similarity-reasoning-ℝ
      x +ℝ (y -ℝ x)
      ~ℝ x +ℝ (neg-ℝ x +ℝ y)
        by sim-eq-ℝ (ap-add-ℝ refl (commutative-add-ℝ _ _))
      ~ℝ y
        by cancel-left-add-diff-ℝ x y
```

### If `x - y = z`, then `x - z = y`

```agda
abstract
  transpose-sim-right-diff-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    sim-ℝ (x -ℝ y) z → sim-ℝ (x -ℝ z) y
  transpose-sim-right-diff-ℝ x y z x-y=z =
    similarity-reasoning-ℝ
      x -ℝ z
      ~ℝ x -ℝ (x -ℝ y)
        by preserves-sim-diff-ℝ (refl-sim-ℝ x) (symmetric-sim-ℝ x-y=z)
      ~ℝ y
        by right-diff-diff-ℝ x y

  transpose-eq-right-diff-ℝ :
    {l : Level} (x : ℝ l) (y : ℝ l) (z : ℝ l) →
    x -ℝ y ＝ z → x -ℝ z ＝ y
  transpose-eq-right-diff-ℝ x y z x-y=z =
    eq-sim-ℝ (transpose-sim-right-diff-ℝ x y z (sim-eq-ℝ x-y=z))
```
