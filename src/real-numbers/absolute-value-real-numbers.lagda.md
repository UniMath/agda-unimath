# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.short-functions-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The
{{#concept "absolute value" Disambiguation="of a real number" Agda=abs-ℝ WD="absolute value" WDID=Q120812}}
of a [real number](real-numbers.dedekind-real-numbers.md) is the
[maximum](real-numbers.maximum-real-numbers.md) of it and its
[negation](real-numbers.negation-real-numbers.md). The absolute value is a
[short function](metric-spaces.short-functions-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

```agda
opaque
  abs-ℝ : {l : Level} → ℝ l → ℝ l
  abs-ℝ x = max-ℝ x (neg-ℝ x)
```

## Properties

### The absolute value preserves similarity

```agda
opaque
  unfolding abs-ℝ

  preserves-sim-abs-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {x' : ℝ l2} → sim-ℝ x x' →
    sim-ℝ (abs-ℝ x) (abs-ℝ x')
  preserves-sim-abs-ℝ x~x' =
    preserves-sim-max-ℝ _ _ x~x' _ _ (preserves-sim-neg-ℝ x~x')
```

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
    ap (max-ℝ (neg-ℝ x)) (neg-neg-ℝ x) ∙ commutative-max-ℝ _ _
```

### `x` is between `-|x|` and `|x|`

```agda
module _
  {l : Level} (x : ℝ l)
  where

  opaque
    unfolding abs-ℝ

    leq-abs-ℝ : leq-ℝ x (abs-ℝ x)
    leq-abs-ℝ = leq-left-max-ℝ x (neg-ℝ x)

    neg-leq-abs-ℝ : leq-ℝ (neg-ℝ x) (abs-ℝ x)
    neg-leq-abs-ℝ = leq-right-max-ℝ x (neg-ℝ x)

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
    leq-abs-leq-leq-neg-ℝ = leq-max-leq-leq-ℝ x (neg-ℝ x) y
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

### The absolute value is a short function

```agda
module _
  {l : Level}
  where

  abstract
    is-short-abs-ℝ :
      is-short-function-Metric-Space
        ( metric-space-leq-ℝ l)
        ( metric-space-leq-ℝ l)
        ( abs-ℝ)
    is-short-abs-ℝ d x y I =
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( abs-ℝ x)
        ( abs-ℝ y)
        ( leq-abs-leq-leq-neg-ℝ
          ( x)
          ( abs-ℝ y +ℝ real-ℚ (rational-ℚ⁺ d))
          ( transitive-leq-ℝ
            ( x)
            ( y +ℝ real-ℚ (rational-ℚ⁺ d))
            ( abs-ℝ y +ℝ real-ℚ (rational-ℚ⁺ d))
            ( preserves-leq-right-add-ℝ
              ( real-ℚ (rational-ℚ⁺ d))
              ( y)
              ( abs-ℝ y)
              ( leq-abs-ℝ y))
            ( left-real-bound-neighborhood-leq-ℝ d x y I))
          ( transitive-leq-ℝ
            ( neg-ℝ x)
            ( neg-ℝ y +ℝ real-ℚ (rational-ℚ⁺ d))
            ( abs-ℝ y +ℝ real-ℚ (rational-ℚ⁺ d))
            ( preserves-leq-right-add-ℝ
              ( real-ℚ (rational-ℚ⁺ d))
              ( neg-ℝ y)
              ( abs-ℝ y)
              ( neg-leq-abs-ℝ y))
            ( reverses-lower-neighborhood-leq-neg-ℝ
              ( d)
              ( y)
              ( x)
              ( right-real-bound-neighborhood-leq-ℝ d x y I))))
        ( leq-abs-leq-leq-neg-ℝ
          ( y)
          ( abs-ℝ x +ℝ real-ℚ (rational-ℚ⁺ d))
          ( transitive-leq-ℝ
            ( y)
            ( x +ℝ real-ℚ (rational-ℚ⁺ d))
            ( abs-ℝ x +ℝ real-ℚ (rational-ℚ⁺ d))
            ( preserves-leq-right-add-ℝ
              ( real-ℚ (rational-ℚ⁺ d))
              ( x)
              ( abs-ℝ x)
              ( leq-abs-ℝ x))
            ( right-real-bound-neighborhood-leq-ℝ d x y I))
          ( transitive-leq-ℝ
            ( neg-ℝ y)
            ( neg-ℝ x +ℝ real-ℚ (rational-ℚ⁺ d))
            ( abs-ℝ x +ℝ real-ℚ (rational-ℚ⁺ d))
            ( preserves-leq-right-add-ℝ
              ( real-ℚ (rational-ℚ⁺ d))
              ( neg-ℝ x)
              ( abs-ℝ x)
              ( neg-leq-abs-ℝ x))
            ( reverses-lower-neighborhood-leq-neg-ℝ
              ( d)
              ( x)
              ( y)
              ( left-real-bound-neighborhood-leq-ℝ d x y I))))

  short-abs-ℝ :
    short-function-Metric-Space (metric-space-leq-ℝ l) (metric-space-leq-ℝ l)
  short-abs-ℝ = (abs-ℝ , is-short-abs-ℝ)
```
