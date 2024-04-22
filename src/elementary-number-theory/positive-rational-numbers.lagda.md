# Positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.submonoids-commutative-monoids
open import group-theory.subsemigroups
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be {{#concept "positive" Disambiguation="rational number" Agda=is-positive-ℚ}}
if its underlying fraction is
[positive](elementary-number-theory.positive-integer-fractions.md).

## Definitions

### The property of being a positive rational number

```agda
module _
  (x : ℚ)
  where

  is-positive-ℚ : UU lzero
  is-positive-ℚ = is-positive-fraction-ℤ (fraction-ℚ x)

  is-prop-is-positive-ℚ : is-prop is-positive-ℚ
  is-prop-is-positive-ℚ = is-prop-is-positive-fraction-ℤ (fraction-ℚ x)

  is-positive-prop-ℚ : Prop lzero
  pr1 is-positive-prop-ℚ = is-positive-ℚ
  pr2 is-positive-prop-ℚ = is-prop-is-positive-ℚ
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

### The positive rational numbers are a Set

```agda
is-set-ℚ⁺ : is-set ℚ⁺
is-set-ℚ⁺ = is-set-type-subtype is-positive-prop-ℚ is-set-ℚ
```

### The rational image of a positive integer is positive

```agda
abstract
  is-positive-rational-ℤ :
    (x : ℤ) → is-positive-ℤ x → is-positive-ℚ (rational-ℤ x)
  is-positive-rational-ℤ x P = P

one-ℚ⁺ : ℚ⁺
one-ℚ⁺ = (one-ℚ , is-positive-int-positive-ℤ one-positive-ℤ)
```

### The rational image of a positive integer fraction is positive

```agda
abstract
  is-positive-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-positive-fraction-ℤ x) →
    is-positive-ℚ (rational-fraction-ℤ x)
  is-positive-rational-fraction-ℤ = is-positive-reduce-fraction-ℤ
```

### A rational number `x` is positive if and only if `0 < x`

```agda
module _
  (x : ℚ)
  where

  abstract
    le-zero-is-positive-ℚ : is-positive-ℚ x → le-ℚ zero-ℚ x
    le-zero-is-positive-ℚ =
      is-positive-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

    is-positive-le-zero-ℚ : le-ℚ zero-ℚ x → is-positive-ℚ x
    is-positive-le-zero-ℚ =
      is-positive-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))
```

### A nonzero rational number or its negative is positive

```agda
decide-is-negative-is-positive-is-nonzero-ℚ :
  {x : ℚ} → is-nonzero-ℚ x → is-positive-ℚ (neg-ℚ x) + is-positive-ℚ x
decide-is-negative-is-positive-is-nonzero-ℚ {x} H =
  rec-coproduct
    ( inl ∘ is-positive-neg-is-negative-ℤ)
    ( inr)
    ( decide-sign-nonzero-ℤ
      { numerator-ℚ x}
      (is-nonzero-numerator-is-nonzero-ℚ x H))
```

### A rational and its negative are not both positive

```agda
abstract
  not-is-negative-is-positive-ℚ :
    (x : ℚ) → ¬ (is-positive-ℚ (neg-ℚ x) × is-positive-ℚ x)
  not-is-negative-is-positive-ℚ x (N , P) =
    is-not-negative-and-positive-ℤ
      ( numerator-ℚ x)
      ( ( is-negative-eq-ℤ
          (neg-neg-ℤ (numerator-ℚ x))
          (is-negative-neg-is-positive-ℤ {numerator-ℚ (neg-ℚ x)} N)) ,
        ( P))
```

### Positive rational numbers are nonzero

```agda
abstract
  is-nonzero-is-positive-ℚ : {x : ℚ} → is-positive-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-positive-ℚ {x} H =
    is-nonzero-is-nonzero-numerator-ℚ x
      ( is-nonzero-is-positive-ℤ
        { numerator-ℚ x}
        ( H))

nonzero-ℚ⁺ : positive-ℚ → nonzero-ℚ
nonzero-ℚ⁺ (x , P) = (x , is-nonzero-is-positive-ℚ P)
```

### The sum of two positive rational numbers is positive

```agda
abstract
  is-positive-add-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-positive-ℚ y → is-positive-ℚ (x +ℚ y)
  is-positive-add-ℚ {x} {y} P Q =
    is-positive-rational-fraction-ℤ
      ( is-positive-add-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( P)
        ( Q))
```

### The positive rational numbers are an additive subsemigroup of the rational numbers

```agda
subsemigroup-add-ℚ⁺ : Subsemigroup lzero semigroup-add-ℚ
pr1 subsemigroup-add-ℚ⁺ = is-positive-prop-ℚ
pr2 subsemigroup-add-ℚ⁺ {x} {y} = is-positive-add-ℚ {x} {y}

semigroup-add-ℚ⁺ : Semigroup lzero
semigroup-add-ℚ⁺ =
  semigroup-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺
```

### The positive sum of two positive rational numbers

```agda
add-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
add-ℚ⁺ = mul-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺

infixl 35 _+ℚ⁺_
_+ℚ⁺_ = add-ℚ⁺
```

### The product of two positive rational numbers is positive

```agda
abstract
  is-positive-mul-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-positive-ℚ y → is-positive-ℚ (x *ℚ y)
  is-positive-mul-ℚ {x} {y} P Q =
    is-positive-rational-fraction-ℤ
      ( is-positive-mul-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( P)
        ( Q))
```

### The positive rational numbers are a multiplicative submonoid of the rational numbers

```agda
is-submonoid-mul-ℚ⁺ :
  is-submonoid-subset-Monoid monoid-mul-ℚ is-positive-prop-ℚ
pr1 is-submonoid-mul-ℚ⁺ = is-positive-rational-ℚ⁺ one-ℚ⁺
pr2 is-submonoid-mul-ℚ⁺ x y = is-positive-mul-ℚ {x} {y}

submonoid-mul-ℚ⁺ : Submonoid lzero monoid-mul-ℚ
pr1 submonoid-mul-ℚ⁺ = is-positive-prop-ℚ
pr2 submonoid-mul-ℚ⁺ = is-submonoid-mul-ℚ⁺

monoid-mul-ℚ⁺ : Monoid lzero
monoid-mul-ℚ⁺ = monoid-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

commutative-monoid-mul-ℚ⁺ : Commutative-Monoid lzero
commutative-monoid-mul-ℚ⁺ =
  commutative-monoid-Commutative-Submonoid
    commutative-monoid-mul-ℚ
    submonoid-mul-ℚ⁺
```

### The positive product of two positive rational numbers

```agda
mul-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
mul-ℚ⁺ = mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

infixl 40 _*ℚ⁺_
_*ℚ⁺_ = mul-ℚ⁺
```

### The positive product of positive rational numbers is commutative

```agda
commutative-mul-ℚ⁺ : (x y : ℚ⁺) → (x *ℚ⁺ y) ＝ (y *ℚ⁺ x)
commutative-mul-ℚ⁺ =
  commutative-mul-Commutative-Submonoid
    commutative-monoid-mul-ℚ
    submonoid-mul-ℚ⁺
```

### The positive rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
module _
  (x : ℚ) (P : is-positive-ℚ x)
  where

  inv-is-positive-ℚ : ℚ
  pr1 inv-is-positive-ℚ = inv-is-positive-fraction-ℤ (fraction-ℚ x) P
  pr2 inv-is-positive-ℚ =
    is-reduced-inv-is-positive-fraction-ℤ
      ( fraction-ℚ x)
      ( P)
      ( is-reduced-fraction-ℚ x)

  abstract
    left-inverse-law-mul-is-positive-ℚ : inv-is-positive-ℚ *ℚ x ＝ one-ℚ
    left-inverse-law-mul-is-positive-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( inv-is-positive-fraction-ℤ (fraction-ℚ x) P)
          ( fraction-ℚ x))
        ( one-fraction-ℤ)
        ( left-inverse-law-mul-is-positive-fraction-ℤ (fraction-ℚ x) P)) ∙
      ( is-retraction-rational-fraction-ℚ one-ℚ)

    right-inverse-law-mul-is-positive-ℚ : x *ℚ inv-is-positive-ℚ ＝ one-ℚ
    right-inverse-law-mul-is-positive-ℚ =
      (commutative-mul-ℚ x _) ∙ (left-inverse-law-mul-is-positive-ℚ)

  is-invertible-is-positive-ℚ : is-invertible-element-Monoid monoid-mul-ℚ x
  pr1 is-invertible-is-positive-ℚ = inv-is-positive-ℚ
  pr1 (pr2 is-invertible-is-positive-ℚ) = right-inverse-law-mul-is-positive-ℚ
  pr2 (pr2 is-invertible-is-positive-ℚ) = left-inverse-law-mul-is-positive-ℚ
```
