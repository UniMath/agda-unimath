# Multiplication by positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.submonoids-commutative-monoids
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of positive rational numbers" Agda=mul-ℚ⁺}}
of two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is their [product](elementary-number-theory.multiplication-rational-numbers.md)
as [rational numbers](elementary-number-theory.rational-numbers.md), and is
itself positive.

## Definition

### The product of two positive rational numbers is positive

```agda
opaque
  unfolding is-positive-ℚ mul-ℚ

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

semigroup-mul-ℚ⁺ : Semigroup lzero
semigroup-mul-ℚ⁺ = semigroup-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

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

## Properties

### The positive product of positive rational numbers is associative

```agda
associative-mul-ℚ⁺ : (x y z : ℚ⁺) → ((x *ℚ⁺ y) *ℚ⁺ z) ＝ (x *ℚ⁺ (y *ℚ⁺ z))
associative-mul-ℚ⁺ =
  associative-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺
```

### The positive product of positive rational numbers is commutative

```agda
commutative-mul-ℚ⁺ : (x y : ℚ⁺) → (x *ℚ⁺ y) ＝ (y *ℚ⁺ x)
commutative-mul-ℚ⁺ =
  commutative-mul-Commutative-Submonoid
    commutative-monoid-mul-ℚ
    submonoid-mul-ℚ⁺
```

### Multiplicative unit laws for positive multiplication of positive rational numbers

```agda
left-unit-law-mul-ℚ⁺ : (x : ℚ⁺) → one-ℚ⁺ *ℚ⁺ x ＝ x
left-unit-law-mul-ℚ⁺ =
  left-unit-law-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

right-unit-law-mul-ℚ⁺ : (x : ℚ⁺) → x *ℚ⁺ one-ℚ⁺ ＝ x
right-unit-law-mul-ℚ⁺ =
  right-unit-law-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺
```

### The positive rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
module _
  (x : ℚ) (P : is-positive-ℚ x)
  where

  opaque
    unfolding is-positive-ℚ mul-ℚ

    inv-is-positive-ℚ : ℚ
    pr1 inv-is-positive-ℚ = inv-is-positive-fraction-ℤ (fraction-ℚ x) P
    pr2 inv-is-positive-ℚ =
      is-reduced-inv-is-positive-fraction-ℤ
        ( fraction-ℚ x)
        ( P)
        ( is-reduced-fraction-ℚ x)

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

    eq-numerator-inv-denominator-is-positive-ℚ :
      numerator-ℚ (inv-is-positive-ℚ) ＝ denominator-ℚ x
    eq-numerator-inv-denominator-is-positive-ℚ = refl

    eq-denominator-inv-numerator-is-positive-ℚ :
      denominator-ℚ (inv-is-positive-ℚ) ＝ numerator-ℚ x
    eq-denominator-inv-numerator-is-positive-ℚ = refl

  is-mul-invertible-is-positive-ℚ : is-invertible-element-Monoid monoid-mul-ℚ x
  pr1 is-mul-invertible-is-positive-ℚ = inv-is-positive-ℚ
  pr1 (pr2 is-mul-invertible-is-positive-ℚ) =
    right-inverse-law-mul-is-positive-ℚ
  pr2 (pr2 is-mul-invertible-is-positive-ℚ) =
    left-inverse-law-mul-is-positive-ℚ
```

### Multiplication on the positive rational numbers distributes over addition

```agda
module _
  (x y z : ℚ⁺)
  where

  left-distributive-mul-add-ℚ⁺ : x *ℚ⁺ (y +ℚ⁺ z) ＝ (x *ℚ⁺ y) +ℚ⁺ (x *ℚ⁺ z)
  left-distributive-mul-add-ℚ⁺ =
    eq-ℚ⁺
      ( left-distributive-mul-add-ℚ
        ( rational-ℚ⁺ x)
        ( rational-ℚ⁺ y)
        ( rational-ℚ⁺ z))

  right-distributive-mul-add-ℚ⁺ : (x +ℚ⁺ y) *ℚ⁺ z ＝ (x *ℚ⁺ z) +ℚ⁺ (y *ℚ⁺ z)
  right-distributive-mul-add-ℚ⁺ =
    eq-ℚ⁺
      ( right-distributive-mul-add-ℚ
        ( rational-ℚ⁺ x)
        ( rational-ℚ⁺ y)
        ( rational-ℚ⁺ z))
```

### Multiplication by a positive rational number preserves strict inequality

```agda
opaque
  unfolding is-positive-ℚ le-ℚ-Prop mul-ℚ

  preserves-le-left-mul-ℚ⁺ :
    (p : ℚ⁺) (q r : ℚ) →
    le-ℚ q r →
    le-ℚ (rational-ℚ⁺ p *ℚ q) (rational-ℚ⁺ p *ℚ r)
  preserves-le-left-mul-ℚ⁺
    p⁺@((p@(p-num , p-denom , p-denom-pos) , _) , p-num-pos)
    q@((q-num , q-denom , _) , _)
    r@((r-num , r-denom , _) , _)
    q<r =
      preserves-le-rational-fraction-ℤ
        ( mul-fraction-ℤ p (fraction-ℚ q))
        ( mul-fraction-ℤ p (fraction-ℚ r))
        ( binary-tr
          ( le-ℤ)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( preserves-le-right-mul-positive-ℤ
            ( mul-positive-ℤ (p-num , p-num-pos) (p-denom , p-denom-pos))
            ( q-num *ℤ r-denom)
            ( r-num *ℤ q-denom)
            ( q<r)))

  preserves-le-right-mul-ℚ⁺ :
    (p : ℚ⁺) (q r : ℚ) →
    le-ℚ q r →
    le-ℚ (q *ℚ rational-ℚ⁺ p) (r *ℚ rational-ℚ⁺ p)
  preserves-le-right-mul-ℚ⁺ p⁺@(p , _) q r q<r =
    binary-tr
      ( le-ℚ)
      ( commutative-mul-ℚ p q)
      ( commutative-mul-ℚ p r)
      ( preserves-le-left-mul-ℚ⁺ p⁺ q r q<r)
```

### Multiplication by a positive rational number preserves inequality

```agda
opaque
  unfolding is-positive-ℚ leq-ℚ-Prop mul-ℚ

  preserves-leq-left-mul-ℚ⁺ :
    (p : ℚ⁺) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (rational-ℚ⁺ p *ℚ q) (rational-ℚ⁺ p *ℚ r)
  preserves-leq-left-mul-ℚ⁺
    p⁺@((p@(p-num , p-denom , p-denom-pos) , _) , p-num-pos)
    q@((q-num , q-denom , _) , _)
    r@((r-num , r-denom , _) , _)
    q≤r =
      preserves-leq-rational-fraction-ℤ
        ( mul-fraction-ℤ p (fraction-ℚ q))
        ( mul-fraction-ℤ p (fraction-ℚ r))
        ( binary-tr
          ( leq-ℤ)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( preserves-leq-right-mul-nonnegative-ℤ
            ( nonnegative-positive-ℤ
              ( mul-positive-ℤ (p-num , p-num-pos) (p-denom , p-denom-pos)))
            ( q-num *ℤ r-denom)
            ( r-num *ℤ q-denom)
            ( q≤r)))

abstract
  preserves-leq-right-mul-ℚ⁺ :
    (p : ℚ⁺) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (q *ℚ rational-ℚ⁺ p) (r *ℚ rational-ℚ⁺ p)
  preserves-leq-right-mul-ℚ⁺ p q r q≤r =
    binary-tr
      ( leq-ℚ)
      ( commutative-mul-ℚ (rational-ℚ⁺ p) q)
      ( commutative-mul-ℚ (rational-ℚ⁺ p) r)
      ( preserves-leq-left-mul-ℚ⁺ p q r q≤r)
```

### Multiplication of a positive rational by another positive rational less than 1 is a strictly deflationary map

```agda
abstract
  le-left-mul-less-than-one-ℚ⁺ :
    (p : ℚ⁺) → le-ℚ⁺ p one-ℚ⁺ → (q : ℚ⁺) → le-ℚ⁺ (p *ℚ⁺ q) q
  le-left-mul-less-than-one-ℚ⁺ p p<1 q =
    tr
      ( le-ℚ⁺ ( p *ℚ⁺ q))
      ( left-unit-law-mul-ℚ⁺ q)
      ( preserves-le-right-mul-ℚ⁺ q (rational-ℚ⁺ p) one-ℚ p<1)

  le-right-mul-less-than-one-ℚ⁺ :
    (p : ℚ⁺) → le-ℚ⁺ p one-ℚ⁺ → (q : ℚ⁺) → le-ℚ⁺ (q *ℚ⁺ p) q
  le-right-mul-less-than-one-ℚ⁺ p p<1 q =
    tr
      ( λ r → le-ℚ⁺ r q)
      ( commutative-mul-ℚ⁺ p q)
      ( le-left-mul-less-than-one-ℚ⁺ p p<1 q)
```
