# Squares in the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.squares-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Definition

```agda
square-ℚ : ℚ → ℚ
square-ℚ a = mul-ℚ a a

is-square-ℚ : ℚ → UU lzero
is-square-ℚ a = Σ ℚ (λ x → a ＝ square-ℚ x)

square-root-ℚ : (a : ℚ) → is-square-ℚ a → ℚ
square-root-ℚ _ (root , _) = root
```

## Properties

### Squares in ℚ are nonnegative

```agda
is-nonnegative-square-ℚ : (a : ℚ) → is-nonnegative-ℚ (square-ℚ a)
is-nonnegative-square-ℚ a =
  rec-coproduct
    ( λ H →
      is-nonnegative-is-positive-ℚ
        ( a *ℚ a)
        ( is-positive-mul-negative-ℚ {a} {a} H H))
    ( λ H → is-nonnegative-mul-nonnegative-ℚ {a} {a} H H)
    ( decide-is-negative-is-nonnegative-ℚ a)
```

### The square of the negation of `x` is the square of `x`

```agda
abstract
  square-neg-ℚ : (x : ℚ) → square-ℚ (neg-ℚ x) ＝ square-ℚ x
  square-neg-ℚ x =
    equational-reasoning
      neg-ℚ x *ℚ neg-ℚ x
      ＝ neg-ℚ (x *ℚ neg-ℚ x) by left-negative-law-mul-ℚ x (neg-ℚ x)
      ＝ neg-ℚ (neg-ℚ (x *ℚ x)) by ap neg-ℚ (right-negative-law-mul-ℚ x x)
      ＝ x *ℚ x by neg-neg-ℚ (x *ℚ x)
```

### Being a square in ℚ is decidable

Has yet to be proved.

### The square of a sum

We have the identity `(x + y)² = x² + 2xy + y²` for the square of a sum.

```agda
abstract
  square-add-ℚ :
    (x y : ℚ) →
    square-ℚ (x +ℚ y) ＝
    square-ℚ x +ℚ (rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
  square-add-ℚ x y =
    equational-reasoning
      square-ℚ (x +ℚ y)
      ＝ x *ℚ (x +ℚ y) +ℚ y *ℚ (x +ℚ y)
        by right-distributive-mul-add-ℚ x y (x +ℚ y)
      ＝ (x *ℚ x +ℚ x *ℚ y) +ℚ (y *ℚ x +ℚ y *ℚ y)
        by
          ap-add-ℚ
            ( left-distributive-mul-add-ℚ x x y)
            ( left-distributive-mul-add-ℚ y x y)
      ＝ x *ℚ x +ℚ (x *ℚ y +ℚ (y *ℚ x +ℚ y *ℚ y))
        by associative-add-ℚ (x *ℚ x) (x *ℚ y) _
      ＝ x *ℚ x +ℚ (x *ℚ y +ℚ (x *ℚ y +ℚ y *ℚ y))
        by
          ap
            ( x *ℚ x +ℚ_)
            ( ap (x *ℚ y +ℚ_) (ap (_+ℚ y *ℚ y) (commutative-mul-ℚ y x)))
      ＝ x *ℚ x +ℚ ((x *ℚ y +ℚ x *ℚ y) +ℚ y *ℚ y)
        by ap (x *ℚ x +ℚ_) (inv (associative-add-ℚ _ _ _))
      ＝ x *ℚ x +ℚ (rational-ℕ 2 *ℚ (x *ℚ y) +ℚ y *ℚ y)
        by ap (λ z → x *ℚ x +ℚ (z +ℚ y *ℚ y)) (inv (mul-two-ℚ _))
      ＝ x *ℚ x +ℚ rational-ℕ 2 *ℚ (x *ℚ y) +ℚ y *ℚ y
        by inv (associative-add-ℚ (x *ℚ x) (rational-ℕ 2 *ℚ (x *ℚ y)) _)
```

### The square of a difference

We have the identity `(x - y)² = x² - 2xy + y²` for the square of a difference.

```agda
abstract
  square-diff-ℚ :
    (x y : ℚ) →
    square-ℚ (x -ℚ y) ＝
    square-ℚ x -ℚ (rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
  square-diff-ℚ x y =
    equational-reasoning
      square-ℚ (x -ℚ y)
      ＝ square-ℚ x +ℚ rational-ℕ 2 *ℚ (x *ℚ neg-ℚ y) +ℚ square-ℚ (neg-ℚ y)
        by square-add-ℚ x (neg-ℚ y)
      ＝ square-ℚ x +ℚ (rational-ℕ 2 *ℚ neg-ℚ (x *ℚ y)) +ℚ square-ℚ y
        by
          ap-add-ℚ
            ( ap
              ( x *ℚ x +ℚ_)
              ( ap (rational-ℕ 2 *ℚ_) (right-negative-law-mul-ℚ x y)))
            ( square-neg-ℚ y)
      ＝ square-ℚ x -ℚ (rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
        by
          ap
            ( λ z → square-ℚ x +ℚ z +ℚ square-ℚ y)
            ( right-negative-law-mul-ℚ (rational-ℕ 2) (x *ℚ y))
```

### If a rational number is positive, so is its square

```agda
abstract
  is-positive-square-positive-ℚ :
    (x : ℚ) → is-positive-ℚ x → is-positive-ℚ (square-ℚ x)
  is-positive-square-positive-ℚ x pos-x =
    is-positive-mul-ℚ {x} {x} pos-x pos-x
```

### If a rational number is negative, its square is positive

```agda
abstract
  is-positive-square-negative-ℚ :
    (x : ℚ) → is-negative-ℚ x → is-positive-ℚ (square-ℚ x)
  is-positive-square-negative-ℚ x neg-x =
    is-positive-mul-negative-ℚ {x} {x} neg-x neg-x
```

### If the square of a rational number is 0, it is zero

```agda
abstract
  is-zero-square-is-zero-ℚ : (x : ℚ) → square-ℚ x ＝ zero-ℚ → x ＝ zero-ℚ
  is-zero-square-is-zero-ℚ x x²=0 =
    trichotomy-sign-ℚ
      ( x)
      ( λ neg-x →
        ex-falso
          ( is-not-positive-zero-ℚ
            ( tr is-positive-ℚ x²=0 (is-positive-square-negative-ℚ x neg-x))))
      ( id)
      ( λ pos-x →
        ex-falso
          ( is-not-positive-zero-ℚ
            ( tr is-positive-ℚ x²=0 (is-positive-square-positive-ℚ x pos-x))))
```

### Squares distribute over multiplication

```agda
abstract
  distributive-square-mul-ℚ :
    (x y : ℚ) → square-ℚ (x *ℚ y) ＝ square-ℚ x *ℚ square-ℚ y
  distributive-square-mul-ℚ x y = interchange-law-mul-mul-ℚ x y x y
```
