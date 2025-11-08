# Positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import set-theory.countable-sets
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be {{#concept "positive" Disambiguation="rational number" Agda=is-positive-ℚ}}
if its underlying fraction is
[positive](elementary-number-theory.positive-integer-fractions.md).

Positive rational numbers are a [subsemigroup](group-theory.subsemigroups.md) of
the
[additive monoid of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md)
and a [submonoid](group-theory.submonoids.md) of the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).

## Definitions

### The property of being a positive rational number

```agda
module _
  (x : ℚ)
  where

  opaque
    is-positive-ℚ : UU lzero
    is-positive-ℚ = is-positive-fraction-ℤ (fraction-ℚ x)

    is-prop-is-positive-ℚ : is-prop is-positive-ℚ
    is-prop-is-positive-ℚ = is-prop-is-positive-fraction-ℤ (fraction-ℚ x)

    is-decidable-prop-is-positive-ℚ : is-decidable-prop is-positive-ℚ
    is-decidable-prop-is-positive-ℚ =
      ( is-prop-is-positive-ℚ , is-decidable-is-positive-ℤ (numerator-ℚ x))

  is-positive-prop-ℚ : Prop lzero
  pr1 is-positive-prop-ℚ = is-positive-ℚ
  pr2 is-positive-prop-ℚ = is-prop-is-positive-ℚ

decidable-subtype-positive-ℚ : decidable-subtype lzero ℚ
decidable-subtype-positive-ℚ x =
  ( is-positive-ℚ x , is-decidable-prop-is-positive-ℚ x)
```

### The type of positive rational numbers

```agda
positive-ℚ : UU lzero
positive-ℚ = type-subtype is-positive-prop-ℚ

ℚ⁺ : UU lzero
ℚ⁺ = positive-ℚ

module _
  (x : positive-ℚ)
  where

  rational-ℚ⁺ : ℚ
  rational-ℚ⁺ = pr1 x

  fraction-ℚ⁺ : fraction-ℤ
  fraction-ℚ⁺ = fraction-ℚ rational-ℚ⁺

  numerator-ℚ⁺ : ℤ
  numerator-ℚ⁺ = numerator-ℚ rational-ℚ⁺

  denominator-ℚ⁺ : ℤ
  denominator-ℚ⁺ = denominator-ℚ rational-ℚ⁺

  is-positive-rational-ℚ⁺ : is-positive-ℚ rational-ℚ⁺
  is-positive-rational-ℚ⁺ = pr2 x

  opaque
    unfolding is-positive-ℚ

    is-positive-fraction-ℚ⁺ : is-positive-fraction-ℤ fraction-ℚ⁺
    is-positive-fraction-ℚ⁺ = is-positive-rational-ℚ⁺

    is-positive-numerator-ℚ⁺ : is-positive-ℤ numerator-ℚ⁺
    is-positive-numerator-ℚ⁺ = is-positive-rational-ℚ⁺

  is-positive-denominator-ℚ⁺ : is-positive-ℤ denominator-ℚ⁺
  is-positive-denominator-ℚ⁺ = is-positive-denominator-ℚ rational-ℚ⁺

abstract
  eq-ℚ⁺ : {x y : ℚ⁺} → rational-ℚ⁺ x ＝ rational-ℚ⁺ y → x ＝ y
  eq-ℚ⁺ {x} {y} = eq-type-subtype is-positive-prop-ℚ
```

## Properties

### The positive rational numbers form a set

```agda
set-ℚ⁺ : Set lzero
set-ℚ⁺ = set-subset ℚ-Set is-positive-prop-ℚ

is-set-ℚ⁺ : is-set ℚ⁺
is-set-ℚ⁺ = is-set-type-Set set-ℚ⁺
```

### The set of positive rational numbers is countable

```agda
abstract
  is-countable-set-ℚ⁺ : is-countable set-ℚ⁺
  is-countable-set-ℚ⁺ =
    is-countable-decidable-subset-is-countable
      ( ℚ-Set)
      ( decidable-subtype-positive-ℚ)
      ( is-countable-ℚ)
```

### The rational image of a positive integer is positive

```agda
opaque
  unfolding is-positive-ℚ

  is-positive-rational-ℤ :
    {x : ℤ} → is-positive-ℤ x → is-positive-ℚ (rational-ℤ x)
  is-positive-rational-ℤ = id

positive-rational-positive-ℤ : positive-ℤ → ℚ⁺
positive-rational-positive-ℤ (z , pos-z) =
    ( rational-ℤ z , is-positive-rational-ℤ pos-z)

positive-rational-ℤ⁺ : ℤ⁺ → ℚ⁺
positive-rational-ℤ⁺ = positive-rational-positive-ℤ

one-ℚ⁺ : ℚ⁺
one-ℚ⁺ = positive-rational-ℤ⁺ one-ℤ⁺
```

### The type of positive rational numbers is inhabited

```agda
abstract
  is-inhabited-ℚ⁺ : ║ ℚ⁺ ║₋₁
  is-inhabited-ℚ⁺ = unit-trunc-Prop one-ℚ⁺
```

### The rational image of a positive natural number is positive

```agda
positive-rational-ℕ⁺ : ℕ⁺ → ℚ⁺
positive-rational-ℕ⁺ n = positive-rational-positive-ℤ (positive-int-ℕ⁺ n)

two-ℚ⁺ : ℚ⁺
two-ℚ⁺ = positive-rational-ℕ⁺ (2 , λ ())
```

### The rational image of a positive integer fraction is positive

```agda
opaque
  unfolding is-positive-ℚ rational-fraction-ℤ

  is-positive-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-positive-fraction-ℤ x) →
    is-positive-ℚ (rational-fraction-ℤ x)
  is-positive-rational-fraction-ℤ = is-positive-reduce-fraction-ℤ
```

### A rational number `x` is positive if and only if `0 < x`

```agda
opaque
  unfolding is-positive-ℚ le-ℚ-Prop

  le-zero-is-positive-ℚ : {x : ℚ} → is-positive-ℚ x → le-ℚ zero-ℚ x
  le-zero-is-positive-ℚ {x} =
    is-positive-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

  is-positive-le-zero-ℚ : {x : ℚ} → le-ℚ zero-ℚ x → is-positive-ℚ x
  is-positive-le-zero-ℚ {x} =
    is-positive-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))
```

### Zero is not a positive rational number

```agda
abstract
  is-not-positive-zero-ℚ : ¬ (is-positive-ℚ zero-ℚ)
  is-not-positive-zero-ℚ pos-0 =
    irreflexive-le-ℚ zero-ℚ (le-zero-is-positive-ℚ pos-0)
```

### The difference of a rational number with a lesser rational number is positive

```agda
module _
  {x y : ℚ} (H : le-ℚ x y)
  where

  abstract
    is-positive-diff-le-ℚ : is-positive-ℚ (y -ℚ x)
    is-positive-diff-le-ℚ =
      is-positive-le-zero-ℚ
        ( backward-implication
          ( iff-translate-diff-le-zero-ℚ x y)
          ( H))

  positive-diff-le-ℚ : ℚ⁺
  positive-diff-le-ℚ = y -ℚ x , is-positive-diff-le-ℚ

  left-law-positive-diff-le-ℚ : (rational-ℚ⁺ positive-diff-le-ℚ) +ℚ x ＝ y
  left-law-positive-diff-le-ℚ =
    ( associative-add-ℚ y (neg-ℚ x) x) ∙
    ( inv-tr
      ( λ u → y +ℚ u ＝ y)
      ( left-inverse-law-add-ℚ x)
      ( right-unit-law-add-ℚ y))

  right-law-positive-diff-le-ℚ : x +ℚ (rational-ℚ⁺ positive-diff-le-ℚ) ＝ y
  right-law-positive-diff-le-ℚ =
    commutative-add-ℚ x (y -ℚ x) ∙ left-law-positive-diff-le-ℚ
```

### Positive rational numbers are nonzero

```agda
opaque
  unfolding is-positive-ℚ

  is-nonzero-is-positive-ℚ : {x : ℚ} → is-positive-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-positive-ℚ {x} H =
    is-nonzero-is-nonzero-numerator-ℚ x
      ( is-nonzero-is-positive-ℤ
        { numerator-ℚ x}
        ( H))

nonzero-ℚ⁺ : positive-ℚ → nonzero-ℚ
nonzero-ℚ⁺ (x , P) = (x , is-nonzero-is-positive-ℚ P)
```

### If `p ≤ q` and `p` is positive, then `q` is positive

```agda
abstract
  is-positive-leq-ℚ⁺ :
    (p : ℚ⁺) {q : ℚ} → leq-ℚ (rational-ℚ⁺ p) q → is-positive-ℚ q
  is-positive-leq-ℚ⁺ (p , pos-p) p≤q =
    is-positive-le-zero-ℚ
      ( concatenate-le-leq-ℚ _ _ _ (le-zero-is-positive-ℚ pos-p) p≤q)

  is-positive-le-ℚ⁺ :
    (p : ℚ⁺) {q : ℚ} → le-ℚ (rational-ℚ⁺ p) q → is-positive-ℚ q
  is-positive-le-ℚ⁺ p p<q = is-positive-leq-ℚ⁺ p (leq-le-ℚ p<q)
```
