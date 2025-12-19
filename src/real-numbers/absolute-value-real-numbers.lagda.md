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
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.short-functions-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-negation-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.zero-real-numbers
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

### The absolute value of zero is zero

```agda
abstract opaque
  unfolding abs-ℝ

  abs-zero-ℝ : abs-ℝ zero-ℝ ＝ zero-ℝ
  abs-zero-ℝ = (ap (max-ℝ zero-ℝ) neg-zero-ℝ) ∙ (is-idempotent-max-ℝ zero-ℝ)
```

### The absolute value preserves similarity

```agda
abstract opaque
  unfolding abs-ℝ

  preserves-sim-abs-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {x' : ℝ l2} → sim-ℝ x x' →
    sim-ℝ (abs-ℝ x) (abs-ℝ x')
  preserves-sim-abs-ℝ x~x' =
    preserves-sim-max-ℝ _ _ x~x' _ _ (preserves-sim-neg-ℝ x~x')
```

### The absolute value commutes with raising the universe level of a real number

```agda
abstract
  sim-abs-raise-ℝ :
    {l1 : Level} (l2 : Level) (x : ℝ l1) →
    sim-ℝ (abs-ℝ (raise-ℝ l2 x)) (raise-ℝ l2 (abs-ℝ x))
  sim-abs-raise-ℝ l2 x =
    similarity-reasoning-ℝ
      abs-ℝ (raise-ℝ l2 x)
      ~ℝ abs-ℝ x
        by preserves-sim-abs-ℝ (sim-raise-ℝ' l2 x)
      ~ℝ raise-ℝ l2 (abs-ℝ x)
        by sim-raise-ℝ l2 (abs-ℝ x)

  abs-raise-ℝ :
    {l1 : Level} (l2 : Level) (x : ℝ l1) →
    abs-ℝ (raise-ℝ l2 x) ＝ raise-ℝ l2 (abs-ℝ x)
  abs-raise-ℝ l2 x = eq-sim-ℝ (sim-abs-raise-ℝ l2 x)
```

### The absolute value of a real number is nonnegative

```agda
abstract opaque
  unfolding abs-ℝ leq-ℝ max-ℝ neg-ℝ real-ℚ

  is-nonnegative-abs-ℝ : {l : Level} → (x : ℝ l) → is-nonnegative-ℝ (abs-ℝ x)
  is-nonnegative-abs-ℝ x q q<0 =
    elim-disjunction
      ( lower-cut-ℝ (abs-ℝ x) q)
      ( id)
      ( λ (x<0 , 0<x) →
        ex-falso
          ( is-disjoint-cut-ℝ
            ( x)
            ( zero-ℚ)
            ( tr (is-in-lower-cut-ℝ x) neg-zero-ℚ 0<x , x<0)))
      ( is-located-lower-upper-cut-ℝ (abs-ℝ x) q<0)

nonnegative-abs-ℝ : {l : Level} → ℝ l → ℝ⁰⁺ l
nonnegative-abs-ℝ x = (abs-ℝ x , is-nonnegative-abs-ℝ x)
```

### The absolute value of the negation of a real number is its absolute value

```agda
abstract opaque
  unfolding abs-ℝ

  abs-neg-ℝ : {l : Level} → (x : ℝ l) → abs-ℝ (neg-ℝ x) ＝ abs-ℝ x
  abs-neg-ℝ x =
    ap (max-ℝ (neg-ℝ x)) (neg-neg-ℝ x) ∙ commutative-max-ℝ _ _
```

### The absolute value of a nonnegative real number is itself

```agda
abstract opaque
  unfolding abs-ℝ

  abs-real-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → abs-ℝ (real-ℝ⁰⁺ x) ＝ real-ℝ⁰⁺ x
  abs-real-ℝ⁰⁺ (x , 0≤x) =
    eq-sim-ℝ
      ( right-leq-left-max-ℝ
        ( transitive-leq-ℝ
          ( neg-ℝ x)
          ( zero-ℝ)
          ( x)
          ( 0≤x)
          ( tr (leq-ℝ (neg-ℝ x)) neg-zero-ℝ (neg-leq-ℝ 0≤x))))
```

### The absolute value of a positive real number is itself

```agda
abstract
  abs-real-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → abs-ℝ (real-ℝ⁺ x) ＝ real-ℝ⁺ x
  abs-real-ℝ⁺ x = abs-real-ℝ⁰⁺ (nonnegative-ℝ⁺ x)
```

### The absolute value of a negative real number is its negation

```agda
abstract
  abs-real-ℝ⁻ : {l : Level} (x : ℝ⁻ l) → abs-ℝ (real-ℝ⁻ x) ＝ neg-ℝ (real-ℝ⁻ x)
  abs-real-ℝ⁻ x⁻@(x , _) = inv (abs-neg-ℝ x) ∙ abs-real-ℝ⁺ (neg-ℝ⁻ x⁻)
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
        ( neg-leq-ℝ neg-leq-abs-ℝ)

    neg-leq-neg-abs-ℝ : leq-ℝ (neg-ℝ (abs-ℝ x)) (neg-ℝ x)
    neg-leq-neg-abs-ℝ = neg-leq-ℝ leq-abs-ℝ
```

### If `|x| ＝ 0` then `x ＝ 0`

```agda
module _
  {l : Level} (x : ℝ l) (|x|~0 : is-zero-ℝ (abs-ℝ x))
  where

  abstract
    is-zero-is-zero-abs-ℝ : is-zero-ℝ x
    is-zero-is-zero-abs-ℝ =
      sim-sim-leq-ℝ
        ( transitive-leq-ℝ _ _ _ (leq-sim-ℝ |x|~0) (leq-abs-ℝ x) ,
          binary-tr
            ( leq-ℝ)
            ( neg-zero-ℝ)
            ( neg-neg-ℝ x)
            ( neg-leq-ℝ
              ( transitive-leq-ℝ _ _ _ (leq-sim-ℝ |x|~0) (neg-leq-abs-ℝ x))))

abstract
  eq-zero-eq-zero-abs-ℝ :
    {l : Level} (x : ℝ l) → abs-ℝ x ＝ raise-zero-ℝ l → x ＝ raise-zero-ℝ l
  eq-zero-eq-zero-abs-ℝ {l} x |x|=0 =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ l zero-ℝ)
        ( is-zero-is-zero-abs-ℝ x
          ( transitive-sim-ℝ _ _ _
            ( sim-raise-ℝ' l zero-ℝ)
            ( sim-eq-ℝ |x|=0))))
```

### If `|x| ≤ 0` then `|x| ＝ 0` and `x ＝ 0`

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  abstract
    is-zero-abs-leq-zero-abs-ℝ :
      leq-ℝ (abs-ℝ x) zero-ℝ → is-zero-ℝ (abs-ℝ x)
    is-zero-abs-leq-zero-abs-ℝ |x|≤0 =
      sim-sim-leq-ℝ (|x|≤0 , is-nonnegative-abs-ℝ x)

    is-zero-leq-zero-abs-ℝ : leq-ℝ (abs-ℝ x) zero-ℝ → is-zero-ℝ x
    is-zero-leq-zero-abs-ℝ |x|≤0 =
      is-zero-is-zero-abs-ℝ x (is-zero-abs-leq-zero-abs-ℝ |x|≤0)
```

### If `|x| ≤ ε` for all `ε : ℚ⁺` then `x ＝ 0`

```agda
module _
  {l : Level}
  (x : ℝ l)
  (is-infinitesimal-x : (ε : ℚ⁺) → leq-ℝ (abs-ℝ x) (real-ℚ⁺ ε))
  where

  abstract
    is-zero-is-infinitesimal-abs-ℝ : is-zero-ℝ x
    is-zero-is-infinitesimal-abs-ℝ =
      is-zero-leq-zero-abs-ℝ
        ( x)
        ( saturated-leq-ℝ
          ( abs-ℝ x)
          ( zero-ℝ)
          ( λ ε →
            inv-tr
              ( leq-ℝ (abs-ℝ x))
              ( left-unit-law-add-ℝ (real-ℚ⁺ ε))
              ( is-infinitesimal-x ε)))
```

### If `x ≤ y` and `-x ≤ y`, `|x| ≤ y`

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where

  abstract opaque
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
        ( preserves-leq-add-ℝ (leq-abs-ℝ x) (leq-abs-ℝ y))
        ( inv-tr
          ( λ z → leq-ℝ z (abs-ℝ x +ℝ abs-ℝ y))
          ( distributive-neg-add-ℝ x y)
          ( preserves-leq-add-ℝ (neg-leq-abs-ℝ x) (neg-leq-abs-ℝ y)))
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
      ( is-positive-is-in-upper-cut-ℝ⁰⁺ (nonnegative-abs-ℝ x) (x<q , -x<q) ,
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

### For positive `x`, `|xy| = x|y|`

```agda
abstract
  abs-left-mul-positive-ℝ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) →
    abs-ℝ (real-ℝ⁺ x *ℝ y) ＝ real-ℝ⁺ x *ℝ abs-ℝ y
  abs-left-mul-positive-ℝ x⁺@(x , _) y =
    abs-mul-ℝ x y ∙ ap-mul-ℝ (abs-real-ℝ⁺ x⁺) refl
```

### For any `ε : ℚ⁺`, `|x| - ε < x` or `|x| - ε < -x`

```agda
abstract opaque
  unfolding abs-ℝ

  approximate-below-abs-ℝ :
    {l : Level} (x : ℝ l) (ε : ℚ⁺) →
    disjunction-type
      ( le-ℝ (abs-ℝ x -ℝ real-ℚ⁺ ε) x)
      ( le-ℝ (abs-ℝ x -ℝ real-ℚ⁺ ε) (neg-ℝ x))
  approximate-below-abs-ℝ x = approximate-below-max-ℝ x (neg-ℝ x)
```

### `|x|² = x²`

```agda
abstract
  square-abs-ℝ : {l : Level} (x : ℝ l) → square-ℝ (abs-ℝ x) ＝ square-ℝ x
  square-abs-ℝ x =
    ( ap square-ℝ (eq-abs-sqrt-square-ℝ x)) ∙
    ( eq-real-square-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x))
```
