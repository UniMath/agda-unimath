# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers

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
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "absolute value" Disambiguation="of a real number" Agda=abs-ℝ WD="absolute value" WDID=Q120812}}
of a [real number](real-numbers.dedekind-real-numbers.md) is the
[binary maximum](real-numbers.binary-maximum-real-numbers.md) of it and its
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
  unfolding abs-ℝ leq-ℝ max-ℝ neg-ℚ neg-ℝ real-ℚ

  is-nonnegative-abs-ℝ : {l : Level} → (x : ℝ l) → is-nonnegative-ℝ (abs-ℝ x)
  is-nonnegative-abs-ℝ x q q<0 =
    elim-disjunction
      ( lower-cut-ℝ (abs-ℝ x) q)
      ( id)
      ( λ (x<0 , 0<x) → ex-falso (is-disjoint-cut-ℝ x zero-ℚ (0<x , x<0)))
      ( is-located-lower-upper-cut-ℝ (abs-ℝ x) q zero-ℚ q<0)

nonnegative-abs-ℝ : {l : Level} → ℝ l → ℝ⁰⁺ l
nonnegative-abs-ℝ x = (abs-ℝ x , is-nonnegative-abs-ℝ x)
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
        ( metric-space-ℝ l)
        ( metric-space-ℝ l)
        ( abs-ℝ)
    is-short-abs-ℝ d x y I =
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( abs-ℝ x)
        ( abs-ℝ y)
        ( leq-abs-leq-leq-neg-ℝ
          ( x)
          ( abs-ℝ y +ℝ real-ℚ⁺ d)
          ( transitive-leq-ℝ
            ( x)
            ( y +ℝ real-ℚ⁺ d)
            ( abs-ℝ y +ℝ real-ℚ⁺ d)
            ( preserves-leq-right-add-ℝ
              ( real-ℚ⁺ d)
              ( y)
              ( abs-ℝ y)
              ( leq-abs-ℝ y))
            ( left-leq-real-bound-neighborhood-ℝ d x y I))
          ( transitive-leq-ℝ
            ( neg-ℝ x)
            ( neg-ℝ y +ℝ real-ℚ⁺ d)
            ( abs-ℝ y +ℝ real-ℚ⁺ d)
            ( preserves-leq-right-add-ℝ
              ( real-ℚ⁺ d)
              ( neg-ℝ y)
              ( abs-ℝ y)
              ( neg-leq-abs-ℝ y))
            ( reverses-lower-neighborhood-neg-ℝ
              ( d)
              ( y)
              ( x)
              ( right-leq-real-bound-neighborhood-ℝ d x y I))))
        ( leq-abs-leq-leq-neg-ℝ
          ( y)
          ( abs-ℝ x +ℝ real-ℚ⁺ d)
          ( transitive-leq-ℝ
            ( y)
            ( x +ℝ real-ℚ⁺ d)
            ( abs-ℝ x +ℝ real-ℚ⁺ d)
            ( preserves-leq-right-add-ℝ
              ( real-ℚ⁺ d)
              ( x)
              ( abs-ℝ x)
              ( leq-abs-ℝ x))
            ( right-leq-real-bound-neighborhood-ℝ d x y I))
          ( transitive-leq-ℝ
            ( neg-ℝ y)
            ( neg-ℝ x +ℝ real-ℚ⁺ d)
            ( abs-ℝ x +ℝ real-ℚ⁺ d)
            ( preserves-leq-right-add-ℝ
              ( real-ℚ⁺ d)
              ( neg-ℝ x)
              ( abs-ℝ x)
              ( neg-leq-abs-ℝ x))
            ( reverses-lower-neighborhood-neg-ℝ
              ( d)
              ( x)
              ( y)
              ( left-leq-real-bound-neighborhood-ℝ d x y I))))

  short-abs-ℝ :
    short-function-Metric-Space (metric-space-ℝ l) (metric-space-ℝ l)
  short-abs-ℝ = (abs-ℝ , is-short-abs-ℝ)
```

### The absolute value of `x` is the square root of `x²`

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract opaque
    unfolding abs-ℝ leq-ℝ leq-ℝ' max-ℝ neg-ℝ real-sqrt-ℝ⁰⁺

    leq-abs-sqrt-square-ℝ :
      leq-ℝ (abs-ℝ x) (real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x))
    leq-abs-sqrt-square-ℝ q =
      elim-disjunction
        ( lower-cut-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x) q)
        ( λ q<x is-nonneg-q →
          is-in-lower-cut-square-ℝ x (q , is-nonneg-q) q<x)
        ( λ q<-x is-nonneg-q →
          tr
            ( λ y → is-in-lower-cut-ℝ y (square-ℚ q))
            ( square-neg-ℝ x)
            ( is-in-lower-cut-square-ℝ (neg-ℝ x) (q , is-nonneg-q) q<-x))

    leq-abs-sqrt-square-ℝ' :
      leq-ℝ' (real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x)) (abs-ℝ x)
    leq-abs-sqrt-square-ℝ' q |x|<q@(x<q , -x<q) =
      ( is-positive-is-in-upper-cut-ℝ⁰⁺ (nonnegative-abs-ℝ x) q (x<q , -x<q) ,
        is-in-upper-cut-square-pos-neg-ℝ x q x<q -x<q)

    eq-abs-sqrt-square-ℝ : abs-ℝ x ＝ real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x)
    eq-abs-sqrt-square-ℝ =
      antisymmetric-leq-ℝ
        ( abs-ℝ x)
        ( real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x))
        ( leq-abs-sqrt-square-ℝ)
        ( leq-leq'-ℝ
          ( real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x))
          ( abs-ℝ x)
          ( leq-abs-sqrt-square-ℝ'))
```

### Absolute values distribute over multiplication

The proof from the square root is likely simplest, but this could also be proved
directly.

```agda
abstract
  abs-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    abs-ℝ (x *ℝ y) ＝ abs-ℝ x *ℝ abs-ℝ y
  abs-mul-ℝ x y =
    equational-reasoning
      abs-ℝ (x *ℝ y)
      ＝ real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ (x *ℝ y))
        by eq-abs-sqrt-square-ℝ (x *ℝ y)
      ＝ real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x *ℝ⁰⁺ nonnegative-square-ℝ y)
        by
          ap
            ( real-sqrt-ℝ⁰⁺)
            ( eq-ℝ⁰⁺ _ _ (distributive-square-mul-ℝ x y))
      ＝
        real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x) *ℝ
        real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ y)
        by ap real-ℝ⁰⁺ (distributive-sqrt-mul-ℝ⁰⁺ _ _)
      ＝ abs-ℝ x *ℝ abs-ℝ y
        by inv (ap-mul-ℝ (eq-abs-sqrt-square-ℝ x) (eq-abs-sqrt-square-ℝ y))
```
