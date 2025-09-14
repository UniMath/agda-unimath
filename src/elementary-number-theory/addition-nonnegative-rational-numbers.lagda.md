# Addition on nonnegative rational numbers

```agda
module elementary-number-theory.addition-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
```

</details>

## Idea

The
{{#concept "sum" WDID=Q32043 WD="addition" Disambiguation="nonnegative rational numbers" Agda=add-ℚ⁰⁺}}
of two
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is their [sum](elementary-number-theory.addition-rational-numbers.md) as
[rational numbers](elementary-number-theory.rational-numbers.md), and is itself
nonnegative.

## Definition

```agda
opaque
  unfolding add-ℚ

  is-nonnegative-add-ℚ :
    (p q : ℚ) → is-nonnegative-ℚ p → is-nonnegative-ℚ q →
    is-nonnegative-ℚ (p +ℚ q)
  is-nonnegative-add-ℚ p q nonneg-p nonneg-q =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-add-fraction-ℤ
        { fraction-ℚ p}
        { fraction-ℚ q}
        ( nonneg-p)
        ( nonneg-q))

add-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
add-ℚ⁰⁺ (p , nonneg-p) (q , nonneg-q) =
  ( p +ℚ q , is-nonnegative-add-ℚ p q nonneg-p nonneg-q)

infixl 35 _+ℚ⁰⁺_
_+ℚ⁰⁺_ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
_+ℚ⁰⁺_ = add-ℚ⁰⁺
```
