# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.logical-equivalences
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "absolute value" Disambiguation="of a real number" Agda=abs-ℝ WD="absolute value" WDID=Q120812}}
of a [real number](real-numbers.dedekind-real-numbers.md) is the
[maximum](real-numbers.maximum-real-numbers.md) of it and its
[negation](real-numbers.negation-real-numbers.md).

```agda
opaque
  abs-ℝ : {l : Level} → ℝ l → ℝ l
  abs-ℝ x = binary-max-ℝ x (neg-ℝ x)
```

## Properties

### The absolute value of a real number is nonnegative

```agda
opaque
  unfolding abs-ℝ

  is-nonnegative-abs-ℝ : {l : Level} → (x : ℝ l) → is-nonnegative-ℝ (abs-ℝ x)
  is-nonnegative-abs-ℝ x q q<0 =
    elim-disjunction
      ( lower-cut-ℝ (abs-ℝ x) q)
      ( id)
      ( λ (x<0 , 0<x) → ex-falso (is-disjoint-cut-ℝ x zero-ℚ (0<x , x<0)))
      ( is-located-lower-upper-cut-ℝ (abs-ℝ x) q zero-ℚ q<0)
```

### The absolute value of the negation of a real number is its absolute value

```agda
opaque
  unfolding abs-ℝ

  abs-neg-ℝ : {l : Level} → (x : ℝ l) → abs-ℝ (neg-ℝ x) ＝ abs-ℝ x
  abs-neg-ℝ x =
    ap (binary-max-ℝ (neg-ℝ x)) (neg-neg-ℝ x) ∙ commutative-binary-max-ℝ _ _
```

### `x` is between `-|x|` and `|x|`

```agda
module _
  {l : Level} (x : ℝ l)
  where

  opaque
    unfolding abs-ℝ

    leq-abs-ℝ : leq-ℝ x (abs-ℝ x)
    leq-abs-ℝ = leq-left-binary-max-ℝ x (neg-ℝ x)

    neg-leq-abs-ℝ : leq-ℝ (neg-ℝ x) (abs-ℝ x)
    neg-leq-abs-ℝ = leq-right-binary-max-ℝ x (neg-ℝ x)

    leq-neg-abs-ℝ : leq-ℝ (neg-ℝ (abs-ℝ x)) x
    leq-neg-abs-ℝ =
      tr
        ( leq-ℝ (neg-ℝ (abs-ℝ x)))
        ( neg-neg-ℝ x)
        ( neg-leq-ℝ (neg-ℝ x) (abs-ℝ x) neg-leq-abs-ℝ)

    neg-leq-neg-abs-ℝ : leq-ℝ (neg-ℝ (abs-ℝ x)) (neg-ℝ x)
    neg-leq-neg-abs-ℝ = neg-leq-ℝ x (abs-ℝ x) leq-abs-ℝ
```

### If `x ≤ y` and `-x ≤ y`, `|x| ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding abs-ℝ

    leq-abs-leq-leq-neg-ℝ : leq-ℝ x y → leq-ℝ (neg-ℝ x) y → leq-ℝ (abs-ℝ x) y
    leq-abs-leq-leq-neg-ℝ H K =
      forward-implication
        ( is-least-binary-upper-bound-binary-max-ℝ x (neg-ℝ x) y)
        ( H , K)
```

### Triangle inequality

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    triangle-inequality-abs-ℝ : leq-ℝ (abs-ℝ (x +ℝ y)) (abs-ℝ x +ℝ abs-ℝ y)
    triangle-inequality-abs-ℝ =
      leq-abs-leq-leq-neg-ℝ
        ( x +ℝ y)
        ( abs-ℝ x +ℝ abs-ℝ y)
        ( preserves-leq-add-ℝ
          ( x)
          ( abs-ℝ x)
          ( y)
          ( abs-ℝ y)
          ( leq-abs-ℝ x)
          ( leq-abs-ℝ y))
        ( inv-tr
          ( λ z → leq-ℝ z (abs-ℝ x +ℝ abs-ℝ y))
          ( distributive-neg-add-ℝ x y)
          ( preserves-leq-add-ℝ
            ( neg-ℝ x)
            ( abs-ℝ x)
            ( neg-ℝ y)
            ( abs-ℝ y)
            ( neg-leq-abs-ℝ x)
            ( neg-leq-abs-ℝ y)))
```
