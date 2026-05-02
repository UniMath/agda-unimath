# Addition on nonnegative rational numbers

```agda
module elementary-number-theory.addition-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.transport-along-identifications

open import order-theory.inflationary-maps-posets
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of two nonnegative rational numbers" Agda=add-ℚ⁰⁺}}
of two
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is their [sum](elementary-number-theory.addition-rational-numbers.md) as
[rational numbers](elementary-number-theory.rational-numbers.md), and is itself
nonnegative.

## Definition

```agda
opaque
  unfolding add-ℚ is-nonnegative-ℚ

  is-nonnegative-add-ℚ :
    {p q : ℚ} → is-nonnegative-ℚ p → is-nonnegative-ℚ q →
    is-nonnegative-ℚ (p +ℚ q)
  is-nonnegative-add-ℚ {p} {q} nonneg-p nonneg-q =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-add-fraction-ℤ
        { fraction-ℚ p}
        { fraction-ℚ q}
        ( nonneg-p)
        ( nonneg-q))

add-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
add-ℚ⁰⁺ (p , nonneg-p) (q , nonneg-q) =
  ( p +ℚ q , is-nonnegative-add-ℚ nonneg-p nonneg-q)

infixl 35 _+ℚ⁰⁺_
_+ℚ⁰⁺_ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
_+ℚ⁰⁺_ = add-ℚ⁰⁺
```

## Properties

### Addition of a nonnegative rational number is an increasing map

```agda
abstract
  is-inflationary-map-left-add-rational-ℚ⁰⁺ :
    (p : ℚ⁰⁺) → is-inflationary-map-Poset ℚ-Poset (rational-ℚ⁰⁺ p +ℚ_)
  is-inflationary-map-left-add-rational-ℚ⁰⁺ (p , nonneg-p) q =
    tr
      ( λ r → leq-ℚ r (p +ℚ q))
      ( left-unit-law-add-ℚ q)
      ( preserves-order-left-add-ℚ
        ( q)
        ( zero-ℚ)
        ( p)
        ( leq-zero-is-nonnegative-ℚ nonneg-p))

  is-inflationary-map-right-add-rational-ℚ⁰⁺ :
    (p : ℚ⁰⁺) → is-inflationary-map-Poset ℚ-Poset (_+ℚ rational-ℚ⁰⁺ p)
  is-inflationary-map-right-add-rational-ℚ⁰⁺ p q =
    tr
      ( leq-ℚ q)
      ( commutative-add-ℚ (rational-ℚ⁰⁺ p) q)
      ( is-inflationary-map-left-add-rational-ℚ⁰⁺ p q)
```
