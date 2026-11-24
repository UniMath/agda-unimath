# Squares of nonnegative real numbers

```agda
module real-numbers.squares-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers

open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "square" Disambiguation="of a nonnegative real number" Agda=square-ℝ⁰⁺}}
of a [nonnegative real number](real-numbers.nonnegative-real-numbers.md) `x` is
the nonnegative real number obtained by
[multiplying](real-numbers.multiplication-nonnegative-real-numbers.md) `x` by
itself.

## Definition

```agda
square-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → ℝ⁰⁺ l
square-ℝ⁰⁺ x = x *ℝ⁰⁺ x
```

## Properties

### For nonnegative real numbers, squaring preserves inequality

```agda
abstract
  preserves-leq-square-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → leq-ℝ⁰⁺ x y →
    leq-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℝ⁰⁺ y)
  preserves-leq-square-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) x≤y =
    transitive-leq-ℝ
      ( square-ℝ x)
      ( x *ℝ y)
      ( square-ℝ y)
      ( preserves-leq-right-mul-ℝ⁰⁺ y⁰⁺ x≤y)
      ( preserves-leq-left-mul-ℝ⁰⁺ x⁰⁺ x≤y)
```

### For nonnegative real numbers, squaring preserves strict inequality

```agda
abstract
  preserves-le-square-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → le-ℝ⁰⁺ x y →
    le-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℝ⁰⁺ y)
  preserves-le-square-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) x<y =
    concatenate-leq-le-ℝ
      ( square-ℝ x)
      ( x *ℝ y)
      ( square-ℝ y)
      ( preserves-leq-left-mul-ℝ⁰⁺ x⁰⁺ (leq-le-ℝ x<y))
      ( preserves-le-right-mul-ℝ⁺ (y , is-positive-le-ℝ⁰⁺ x⁰⁺ y x<y) x<y)
```

### For nonnegative real numbers, squaring reflects inequality

```agda
abstract
  reflects-leq-square-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    leq-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℝ⁰⁺ y) → leq-ℝ⁰⁺ x y
  reflects-leq-square-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) x²≤y² =
    leq-not-le-ℝ
      ( y)
      ( x)
      ( λ y<x →
        not-leq-le-ℝ
          ( square-ℝ y)
          ( square-ℝ x)
          ( preserves-le-square-ℝ⁰⁺ y⁰⁺ x⁰⁺ y<x)
          ( x²≤y²))
```

### If a rational `q` is in the upper cut of a nonnegative real number `x`, `q²` is in the upper cut of `x²`

```agda
abstract
  is-in-upper-cut-square-ℝ :
    {l : Level} (x : ℝ⁰⁺ l) (q : ℚ) → is-in-upper-cut-ℝ⁰⁺ x q →
    is-in-upper-cut-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℚ q)
  is-in-upper-cut-square-ℝ x⁰⁺@(x , _) q q∈Ux =
    is-in-upper-cut-le-real-ℚ
      ( square-ℝ x)
      ( tr
        ( le-ℝ (square-ℝ x))
        ( square-real-ℚ q)
        ( preserves-le-square-ℝ⁰⁺
          ( x⁰⁺)
          ( nonnegative-real-ℚ⁺
            ( q , is-positive-is-in-upper-cut-ℝ⁰⁺ x⁰⁺ q∈Ux))
          ( le-real-is-in-upper-cut-ℝ x q∈Ux)))
```

### If a nonnegative rational `q` is in the lower cut of `x`, `q²` is in the lower cut of `x²`

```agda
abstract
  is-in-lower-cut-square-ℝ :
    {l : Level} (x : ℝ l) (q : ℚ⁰⁺) → is-in-lower-cut-ℝ x (rational-ℚ⁰⁺ q) →
    is-in-lower-cut-ℝ (square-ℝ x) (square-ℚ (rational-ℚ⁰⁺ q))
  is-in-lower-cut-square-ℝ x q⁰⁺@(q , _) q∈Lx =
    let
      qℝ = nonnegative-real-ℚ⁰⁺ q⁰⁺
      q<x = le-real-is-in-lower-cut-ℝ x q∈Lx
    in
      is-in-lower-cut-le-real-ℚ
        ( square-ℝ x)
        ( tr
          ( λ y → le-ℝ y (square-ℝ x))
          ( square-real-ℚ q)
          ( preserves-le-square-ℝ⁰⁺
            ( qℝ)
            ( x , is-nonnegative-le-ℝ⁰⁺ qℝ x q<x)
            ( q<x)))
```
