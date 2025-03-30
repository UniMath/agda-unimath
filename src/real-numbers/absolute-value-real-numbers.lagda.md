# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.logical-equivalences
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.propositions
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

The
{{#concept "absolute value" Disambiguation="of a real number" Agda=abs-ℝ WD="absolute value" WDID=Q120812}}
of a [real number](real-numbers.dedekind-real-numbers.md) is the
[maximum](real-numbers.maximum-real-numbers.md) of it and its
[negation](real-numbers.negation-real-numbers.md).

```agda
abs-ℝ : {l : Level} → ℝ l → ℝ l
abs-ℝ x = binary-max-ℝ x (neg-ℝ x)
```

## Properties

### The absolute value of a real number is nonnegative

```agda
abstract
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
abstract
  abs-neg-ℝ : {l : Level} → (x : ℝ l) → abs-ℝ (neg-ℝ x) ＝ abs-ℝ x
  abs-neg-ℝ x =
    ap (binary-max-ℝ (neg-ℝ x)) (neg-neg-ℝ x) ∙ commutative-binary-max-ℝ _ _
```

### `x` is between `-|x|` and `|x|`

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
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

### Two real numbers `x` and `y` are in a `d`-neighborhood of each other if and only if `|x-y| ≤ d`

```agda
abs-diff-bound-neighborhood-leq-ℝ :
  {l : Level} → (d : ℚ⁺) → (x y : ℝ l) → type-Prop (premetric-leq-ℝ l d x y) →
  leq-ℝ (abs-ℝ (x -ℝ y)) (real-ℚ (rational-ℚ⁺ d))
abs-diff-bound-neighborhood-leq-ℝ d⁺@(d , _) x y (H , K) =
  forward-implication
    ( is-least-binary-upper-bound-binary-max-ℝ
      ( x -ℝ y)
      ( neg-ℝ (x -ℝ y))
      ( real-ℚ d))
    ((λ q q<x-y → reflects-le-real-ℚ q d {! le-transpose-right-diff-ℝ (real-ℚ q) x y ?  !}) , {!   !})
```
