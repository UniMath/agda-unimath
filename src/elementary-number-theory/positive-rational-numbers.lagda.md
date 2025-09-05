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
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
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

open import group-theory.commutative-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.submonoids-commutative-monoids
open import group-theory.subsemigroups

open import order-theory.decidable-posets
open import order-theory.decidable-total-orders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
open import order-theory.total-orders
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

### The positive rational numbers form a set

```agda
set-ℚ⁺ : Set lzero
set-ℚ⁺ = set-subset ℚ-Set is-positive-prop-ℚ

is-set-ℚ⁺ : is-set ℚ⁺
is-set-ℚ⁺ = is-set-type-Set set-ℚ⁺
```

### The rational image of a positive integer is positive

```agda
abstract
  is-positive-rational-ℤ :
    (x : ℤ) → is-positive-ℤ x → is-positive-ℚ (rational-ℤ x)
  is-positive-rational-ℤ x P = P

positive-rational-positive-ℤ : positive-ℤ → ℚ⁺
positive-rational-positive-ℤ (z , pos-z) = rational-ℤ z , pos-z

positive-rational-ℤ⁺ : ℤ⁺ → ℚ⁺
positive-rational-ℤ⁺ = positive-rational-positive-ℤ

one-ℚ⁺ : ℚ⁺
one-ℚ⁺ = (one-ℚ , is-positive-int-positive-ℤ one-positive-ℤ)
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
```

### The rational image of a positive integer fraction is positive

```agda
opaque
  unfolding rational-fraction-ℤ

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

  opaque
    unfolding le-ℚ-Prop

    le-zero-is-positive-ℚ : is-positive-ℚ x → le-ℚ zero-ℚ x
    le-zero-is-positive-ℚ =
      is-positive-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

    is-positive-le-zero-ℚ : le-ℚ zero-ℚ x → is-positive-ℚ x
    is-positive-le-zero-ℚ =
      is-positive-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))
```

### Zero is not a positive rational number

```agda
abstract
  is-not-positive-zero-ℚ : ¬ (is-positive-ℚ zero-ℚ)
  is-not-positive-zero-ℚ pos-0 =
    irreflexive-le-ℚ zero-ℚ (le-zero-is-positive-ℚ zero-ℚ pos-0)
```

### The difference of a rational number with a lesser rational number is positive

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  abstract
    is-positive-diff-le-ℚ : is-positive-ℚ (y -ℚ x)
    is-positive-diff-le-ℚ =
      is-positive-le-zero-ℚ
        ( y -ℚ x)
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

### A nonzero rational number or its negative is positive

```agda
opaque
  unfolding neg-ℚ

  decide-is-negative-is-positive-is-nonzero-ℚ :
    {x : ℚ} → is-nonzero-ℚ x → is-positive-ℚ (neg-ℚ x) + is-positive-ℚ x
  decide-is-negative-is-positive-is-nonzero-ℚ {x} H =
    rec-coproduct
      ( inl ∘ is-positive-neg-is-negative-ℤ)
      ( inr)
      ( decide-sign-nonzero-ℤ
        { numerator-ℚ x}
        ( is-nonzero-numerator-is-nonzero-ℚ x H))
```

### A rational and its negative are not both positive

```agda
opaque
  unfolding neg-ℚ

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
opaque
  unfolding add-ℚ

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

add-ℚ⁺' : ℚ⁺ → ℚ⁺ → ℚ⁺
add-ℚ⁺' x y = add-ℚ⁺ y x

infixl 35 _+ℚ⁺_
_+ℚ⁺_ = add-ℚ⁺

ap-add-ℚ⁺ :
  {x y x' y' : ℚ⁺} → x ＝ x' → y ＝ y' → x +ℚ⁺ y ＝ x' +ℚ⁺ y'
ap-add-ℚ⁺ p q = ap-binary add-ℚ⁺ p q
```

### The positive sum of positive rational numbers is associative

```agda
associative-add-ℚ⁺ : (x y z : ℚ⁺) → ((x +ℚ⁺ y) +ℚ⁺ z) ＝ (x +ℚ⁺ (y +ℚ⁺ z))
associative-add-ℚ⁺ =
  associative-mul-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺
```

### The positive sum of positive rational numbers is commutative

```agda
commutative-add-ℚ⁺ : (x y : ℚ⁺) → (x +ℚ⁺ y) ＝ (y +ℚ⁺ x)
commutative-add-ℚ⁺ x y =
  eq-ℚ⁺ (commutative-add-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y))
```

### The additive interchange law on positive rational numbers

```agda
interchange-law-add-add-ℚ⁺ :
  (x y u v : ℚ⁺) → (x +ℚ⁺ y) +ℚ⁺ (u +ℚ⁺ v) ＝ (x +ℚ⁺ u) +ℚ⁺ (y +ℚ⁺ v)
interchange-law-add-add-ℚ⁺ x y u v =
  eq-ℚ⁺
    ( interchange-law-add-add-ℚ
      ( rational-ℚ⁺ x)
      ( rational-ℚ⁺ y)
      ( rational-ℚ⁺ u)
      ( rational-ℚ⁺ v))
```

### The product of two positive rational numbers is positive

```agda
opaque
  unfolding mul-ℚ

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
    unfolding mul-ℚ

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

### The strict inequality on positive rational numbers

```agda
le-prop-ℚ⁺ : ℚ⁺ → ℚ⁺ → Prop lzero
le-prop-ℚ⁺ x y = le-ℚ-Prop (rational-ℚ⁺ x) (rational-ℚ⁺ y)

le-ℚ⁺ : ℚ⁺ → ℚ⁺ → UU lzero
le-ℚ⁺ x y = type-Prop (le-prop-ℚ⁺ x y)

is-prop-le-ℚ⁺ : (x y : ℚ⁺) → is-prop (le-ℚ⁺ x y)
is-prop-le-ℚ⁺ x y = is-prop-type-Prop (le-prop-ℚ⁺ x y)

transitive-le-ℚ⁺ : is-transitive le-ℚ⁺
transitive-le-ℚ⁺ x y z =
  transitive-le-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y) (rational-ℚ⁺ z)

strictly-preordered-set-ℚ⁺ : Strictly-Preordered-Set lzero lzero
pr1 strictly-preordered-set-ℚ⁺ = set-ℚ⁺
pr2 strictly-preordered-set-ℚ⁺ =
  ( le-prop-ℚ⁺) ,
  ( irreflexive-le-ℚ ∘ rational-ℚ⁺) ,
  ( transitive-le-ℚ⁺)

strict-preorder-ℚ⁺ : Strict-Preorder lzero lzero
strict-preorder-ℚ⁺ =
  strict-preorder-Strictly-Preordered-Set strictly-preordered-set-ℚ⁺
```

### The inequality on positive rational numbers

```agda
decidable-total-order-ℚ⁺ : Decidable-Total-Order lzero lzero
decidable-total-order-ℚ⁺ =
  decidable-total-order-Decidable-Total-Suborder
    ℚ-Decidable-Total-Order
    is-positive-prop-ℚ

poset-ℚ⁺ : Poset lzero lzero
poset-ℚ⁺ = poset-Decidable-Total-Order decidable-total-order-ℚ⁺

preorder-ℚ⁺ : Preorder lzero lzero
preorder-ℚ⁺ = preorder-Poset poset-ℚ⁺

is-total-leq-ℚ⁺ : is-total-Poset poset-ℚ⁺
is-total-leq-ℚ⁺ =
  is-total-poset-Decidable-Total-Order decidable-total-order-ℚ⁺

is-decidable-leq-ℚ⁺ : is-decidable-leq-Poset poset-ℚ⁺
is-decidable-leq-ℚ⁺ =
  is-decidable-poset-Decidable-Total-Order decidable-total-order-ℚ⁺

leq-prop-ℚ⁺ : ℚ⁺ → ℚ⁺ → Prop lzero
leq-prop-ℚ⁺ = leq-prop-Poset poset-ℚ⁺

leq-ℚ⁺ : ℚ⁺ → ℚ⁺ → UU lzero
leq-ℚ⁺ = leq-Poset poset-ℚ⁺

is-prop-leq-ℚ⁺ : (x y : ℚ⁺) → is-prop (leq-ℚ⁺ x y)
is-prop-leq-ℚ⁺ x y = is-prop-type-Prop (leq-prop-ℚ⁺ x y)

refl-leq-ℚ⁺ : is-reflexive leq-ℚ⁺
refl-leq-ℚ⁺ = refl-leq-Poset poset-ℚ⁺

transitive-leq-ℚ⁺ : is-transitive leq-ℚ⁺
transitive-leq-ℚ⁺ = transitive-leq-Poset poset-ℚ⁺

antisymmetric-leq-ℚ⁺ : is-antisymmetric leq-ℚ⁺
antisymmetric-leq-ℚ⁺ = antisymmetric-leq-Poset poset-ℚ⁺

leq-le-ℚ⁺ : {x y : ℚ⁺} → le-ℚ⁺ x y → leq-ℚ⁺ x y
leq-le-ℚ⁺ {x} {y} = leq-le-ℚ {rational-ℚ⁺ x} {rational-ℚ⁺ y}
```

### The minimum between two positive rational numbers

```agda
min-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
min-ℚ⁺ = min-Decidable-Total-Order decidable-total-order-ℚ⁺

abstract
  associative-min-ℚ⁺ :
    (x y z : ℚ⁺) → min-ℚ⁺ (min-ℚ⁺ x y) z ＝ min-ℚ⁺ x (min-ℚ⁺ y z)
  associative-min-ℚ⁺ =
    associative-min-Decidable-Total-Order decidable-total-order-ℚ⁺

  commutative-min-ℚ⁺ : (x y : ℚ⁺) → min-ℚ⁺ x y ＝ min-ℚ⁺ y x
  commutative-min-ℚ⁺ =
    commutative-min-Decidable-Total-Order decidable-total-order-ℚ⁺

  idempotent-min-ℚ⁺ : (x : ℚ⁺) → min-ℚ⁺ x x ＝ x
  idempotent-min-ℚ⁺ =
    idempotent-min-Decidable-Total-Order decidable-total-order-ℚ⁺

  leq-left-min-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ (min-ℚ⁺ x y) x
  leq-left-min-ℚ⁺ = leq-left-min-Decidable-Total-Order decidable-total-order-ℚ⁺

  leq-right-min-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ (min-ℚ⁺ x y) y
  leq-right-min-ℚ⁺ =
    leq-right-min-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### The maximum between two positive rational numbers

```agda
max-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
max-ℚ⁺ = max-Decidable-Total-Order decidable-total-order-ℚ⁺

abstract
  associative-max-ℚ⁺ :
    (x y z : ℚ⁺) → max-ℚ⁺ (max-ℚ⁺ x y) z ＝ max-ℚ⁺ x (max-ℚ⁺ y z)
  associative-max-ℚ⁺ =
    associative-max-Decidable-Total-Order decidable-total-order-ℚ⁺

  commutative-max-ℚ⁺ : (x y : ℚ⁺) → max-ℚ⁺ x y ＝ max-ℚ⁺ y x
  commutative-max-ℚ⁺ =
    commutative-max-Decidable-Total-Order decidable-total-order-ℚ⁺

  idempotent-max-ℚ⁺ : (x : ℚ⁺) → max-ℚ⁺ x x ＝ x
  idempotent-max-ℚ⁺ =
    idempotent-max-Decidable-Total-Order decidable-total-order-ℚ⁺

  leq-left-max-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ x (max-ℚ⁺ x y)
  leq-left-max-ℚ⁺ = leq-left-max-Decidable-Total-Order decidable-total-order-ℚ⁺

  leq-right-max-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ y (max-ℚ⁺ x y)
  leq-right-max-ℚ⁺ =
    leq-right-max-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### The sum of two positive rational numbers is greater than each of them

```agda
module _
  (x y : ℚ⁺)
  where

  le-left-add-ℚ⁺ : le-ℚ⁺ x (x +ℚ⁺ y)
  le-left-add-ℚ⁺ =
    tr
      ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
      ( right-unit-law-add-ℚ (rational-ℚ⁺ x))
      ( preserves-le-right-add-ℚ
        ( rational-ℚ⁺ x)
        ( zero-ℚ)
        ( rational-ℚ⁺ y)
        ( le-zero-is-positive-ℚ
          ( rational-ℚ⁺ y)
          ( is-positive-rational-ℚ⁺ y)))

  le-right-add-ℚ⁺ : le-ℚ⁺ y (x +ℚ⁺ y)
  le-right-add-ℚ⁺ =
    tr
      ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
      ( left-unit-law-add-ℚ (rational-ℚ⁺ y))
      ( preserves-le-left-add-ℚ
        ( rational-ℚ⁺ y)
        ( zero-ℚ)
        ( rational-ℚ⁺ x)
        ( le-zero-is-positive-ℚ
          ( rational-ℚ⁺ x)
          ( is-positive-rational-ℚ⁺ x)))
```

### The positive difference of strictly inequal positive rational numbers

```agda
module _
  (x y : ℚ⁺) (H : le-ℚ⁺ x y)
  where

  le-diff-ℚ⁺ : ℚ⁺
  le-diff-ℚ⁺ = positive-diff-le-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y) H

  left-diff-law-add-ℚ⁺ : le-diff-ℚ⁺ +ℚ⁺ x ＝ y
  left-diff-law-add-ℚ⁺ =
    eq-ℚ⁺
      ( ( associative-add-ℚ
          ( rational-ℚ⁺ y)
          ( neg-ℚ (rational-ℚ⁺ x))
          ( rational-ℚ⁺ x)) ∙
        ( ( ap
            ( (rational-ℚ⁺ y) +ℚ_)
            ( left-inverse-law-add-ℚ (rational-ℚ⁺ x))) ∙
        ( right-unit-law-add-ℚ (rational-ℚ⁺ y))))

  right-diff-law-add-ℚ⁺ : x +ℚ⁺ le-diff-ℚ⁺ ＝ y
  right-diff-law-add-ℚ⁺ =
    ( eq-ℚ⁺
      ( commutative-add-ℚ
        ( rational-ℚ⁺ x)
        ( rational-ℚ⁺ le-diff-ℚ⁺))) ∙
    ( left-diff-law-add-ℚ⁺)

  le-le-diff-ℚ⁺ : le-ℚ⁺ le-diff-ℚ⁺ y
  le-le-diff-ℚ⁺ =
    tr
      ( le-ℚ⁺ le-diff-ℚ⁺)
      ( left-diff-law-add-ℚ⁺)
      ( le-left-add-ℚ⁺ le-diff-ℚ⁺ x)
```

### Multiplication by a positive rational number preserves strict inequality

```agda
opaque
  unfolding le-ℚ-Prop
  unfolding mul-ℚ

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
  unfolding leq-ℚ-Prop
  unfolding mul-ℚ

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

### The positive mediant between zero and a positive rational number

```agda
opaque
  mediant-zero-ℚ⁺ : ℚ⁺ → ℚ⁺
  mediant-zero-ℚ⁺ x =
    ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x) ,
      is-positive-le-zero-ℚ
        ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x))
        ( le-left-mediant-ℚ
          ( zero-ℚ)
          ( rational-ℚ⁺ x)
          ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))))

  le-mediant-zero-ℚ⁺ : (x : ℚ⁺) → le-ℚ⁺ (mediant-zero-ℚ⁺ x) x
  le-mediant-zero-ℚ⁺ x =
    le-right-mediant-ℚ
      ( zero-ℚ)
      ( rational-ℚ⁺ x)
      ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))
```

### Any positive rational number is the sum of two positive rational numbers

```agda
module _
  (x : ℚ⁺)
  where

  left-summand-split-ℚ⁺ : ℚ⁺
  left-summand-split-ℚ⁺ = mediant-zero-ℚ⁺ x

  right-summand-split-ℚ⁺ : ℚ⁺
  right-summand-split-ℚ⁺ =
    le-diff-ℚ⁺ (mediant-zero-ℚ⁺ x) x (le-mediant-zero-ℚ⁺ x)

  abstract
    eq-add-split-ℚ⁺ :
      left-summand-split-ℚ⁺ +ℚ⁺ right-summand-split-ℚ⁺ ＝ x
    eq-add-split-ℚ⁺ =
      right-diff-law-add-ℚ⁺ (mediant-zero-ℚ⁺ x) x (le-mediant-zero-ℚ⁺ x)

  split-ℚ⁺ : Σ ℚ⁺ (λ u → Σ ℚ⁺ (λ v → u +ℚ⁺ v ＝ x))
  split-ℚ⁺ =
    left-summand-split-ℚ⁺ ,
    right-summand-split-ℚ⁺ ,
    eq-add-split-ℚ⁺

  abstract
    le-add-split-ℚ⁺ :
      (p q r s : ℚ) →
      le-ℚ p (q +ℚ rational-ℚ⁺ left-summand-split-ℚ⁺) →
      le-ℚ r (s +ℚ rational-ℚ⁺ right-summand-split-ℚ⁺) →
      le-ℚ (p +ℚ r) ((q +ℚ s) +ℚ rational-ℚ⁺ x)
    le-add-split-ℚ⁺ p q r s p<q+left r<s+right =
      tr
        ( le-ℚ (p +ℚ r))
        ( interchange-law-add-add-ℚ
          ( q)
          ( rational-ℚ⁺ left-summand-split-ℚ⁺)
          ( s)
          ( rational-ℚ⁺ right-summand-split-ℚ⁺) ∙
          ap ((q +ℚ s) +ℚ_) (ap rational-ℚ⁺ eq-add-split-ℚ⁺))
        ( preserves-le-add-ℚ
          { p}
          { q +ℚ rational-ℚ⁺ left-summand-split-ℚ⁺}
          { r}
          { s +ℚ rational-ℚ⁺ right-summand-split-ℚ⁺}
          ( p<q+left)
          ( r<s+right))
```

### Any two positive rational numbers have a positive rational number strictly less than both

```agda
module _
  (x y : ℚ⁺)
  where

  mediant-zero-min-ℚ⁺ : ℚ⁺
  mediant-zero-min-ℚ⁺ = mediant-zero-ℚ⁺ (min-ℚ⁺ x y)

  abstract
    le-left-mediant-zero-min-ℚ⁺ : le-ℚ⁺ mediant-zero-min-ℚ⁺ x
    le-left-mediant-zero-min-ℚ⁺ =
      concatenate-le-leq-ℚ
        ( rational-ℚ⁺ mediant-zero-min-ℚ⁺)
        ( rational-ℚ⁺ (min-ℚ⁺ x y))
        ( rational-ℚ⁺ x)
        ( le-mediant-zero-ℚ⁺ (min-ℚ⁺ x y))
        ( leq-left-min-ℚ⁺ x y)

    le-right-mediant-zero-min-ℚ⁺ : le-ℚ⁺ mediant-zero-min-ℚ⁺ y
    le-right-mediant-zero-min-ℚ⁺ =
      concatenate-le-leq-ℚ
        ( rational-ℚ⁺ mediant-zero-min-ℚ⁺)
        ( rational-ℚ⁺ (min-ℚ⁺ x y))
        ( rational-ℚ⁺ y)
        ( le-mediant-zero-ℚ⁺ (min-ℚ⁺ x y))
        ( leq-right-min-ℚ⁺ x y)
```

### Any positive rational number `p` has a `q` with `q + q < p`

```agda
module _
  (p : ℚ⁺)
  where

  modulus-le-double-le-ℚ⁺ : ℚ⁺
  modulus-le-double-le-ℚ⁺ =
    mediant-zero-min-ℚ⁺
      ( left-summand-split-ℚ⁺ p)
      ( right-summand-split-ℚ⁺ p)

  abstract
    le-double-le-modulus-le-double-le-ℚ⁺ :
        le-ℚ⁺
          ( modulus-le-double-le-ℚ⁺ +ℚ⁺ modulus-le-double-le-ℚ⁺)
          ( p)
    le-double-le-modulus-le-double-le-ℚ⁺ =
      tr
        ( le-ℚ⁺ (modulus-le-double-le-ℚ⁺ +ℚ⁺ modulus-le-double-le-ℚ⁺))
        ( eq-add-split-ℚ⁺ p)
        ( preserves-le-add-ℚ
          { rational-ℚ⁺ (modulus-le-double-le-ℚ⁺)}
          { rational-ℚ⁺ (left-summand-split-ℚ⁺ p)}
          { rational-ℚ⁺ (modulus-le-double-le-ℚ⁺)}
          { rational-ℚ⁺ (right-summand-split-ℚ⁺ p)}
          ( le-left-mediant-zero-min-ℚ⁺
            ( left-summand-split-ℚ⁺ p)
            ( right-summand-split-ℚ⁺ p))
          ( le-right-mediant-zero-min-ℚ⁺
            ( left-summand-split-ℚ⁺ p)
            ( right-summand-split-ℚ⁺ p)))

    le-modulus-le-double-le-ℚ⁺ : le-ℚ⁺ modulus-le-double-le-ℚ⁺ p
    le-modulus-le-double-le-ℚ⁺ =
      transitive-le-ℚ⁺
        ( modulus-le-double-le-ℚ⁺)
        ( left-summand-split-ℚ⁺ p)
        ( p)
        ( le-mediant-zero-ℚ⁺ p)
        ( le-left-mediant-zero-min-ℚ⁺
          ( left-summand-split-ℚ⁺ p)
          ( right-summand-split-ℚ⁺ p))

    bound-double-le-ℚ⁺ :
      Σ ℚ⁺ (λ q → le-ℚ⁺ (q +ℚ⁺ q) p)
    bound-double-le-ℚ⁺ =
      ( modulus-le-double-le-ℚ⁺ , le-double-le-modulus-le-double-le-ℚ⁺)

    double-le-ℚ⁺ : exists ℚ⁺ (λ q → le-prop-ℚ⁺ (q +ℚ⁺ q) p)
    double-le-ℚ⁺ = unit-trunc-Prop bound-double-le-ℚ⁺
```

### Addition with a positive rational number is an increasing map

```agda
abstract
  le-left-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ x ((rational-ℚ⁺ d) +ℚ x)
  le-left-add-rational-ℚ⁺ x d =
    concatenate-leq-le-ℚ
      ( x)
      ( zero-ℚ +ℚ x)
      ( (rational-ℚ⁺ d) +ℚ x)
      ( inv-tr (leq-ℚ x) (left-unit-law-add-ℚ x) (refl-leq-ℚ x))
      ( preserves-le-left-add-ℚ
        ( x)
        ( zero-ℚ)
        ( rational-ℚ⁺ d)
        ( le-zero-is-positive-ℚ
          ( rational-ℚ⁺ d)
          ( is-positive-rational-ℚ⁺ d)))

  le-right-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ x (x +ℚ (rational-ℚ⁺ d))
  le-right-add-rational-ℚ⁺ x d =
    inv-tr
      ( le-ℚ x)
      ( commutative-add-ℚ x (rational-ℚ⁺ d))
      ( le-left-add-rational-ℚ⁺ x d)

  leq-left-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → leq-ℚ x (rational-ℚ⁺ d +ℚ x)
  leq-left-add-rational-ℚ⁺ x d = leq-le-ℚ (le-left-add-rational-ℚ⁺ x d)

  leq-right-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → leq-ℚ x (x +ℚ rational-ℚ⁺ d)
  leq-right-add-rational-ℚ⁺ x d = leq-le-ℚ (le-right-add-rational-ℚ⁺ x d)
```

### Subtraction by a positive rational number is a strictly deflationary map

```agda
le-diff-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ (x -ℚ rational-ℚ⁺ d) x
le-diff-rational-ℚ⁺ x d =
  tr
    ( le-ℚ (x -ℚ rational-ℚ⁺ d))
    ( equational-reasoning
      (x -ℚ rational-ℚ⁺ d) +ℚ rational-ℚ⁺ d
      ＝ x +ℚ (neg-ℚ (rational-ℚ⁺ d) +ℚ rational-ℚ⁺ d)
        by associative-add-ℚ x (neg-ℚ (rational-ℚ⁺ d)) (rational-ℚ⁺ d)
      ＝ x +ℚ zero-ℚ
        by ap (x +ℚ_) (left-inverse-law-add-ℚ (rational-ℚ⁺ d))
      ＝ x by right-unit-law-add-ℚ x)
    ( le-right-add-rational-ℚ⁺ (x -ℚ rational-ℚ⁺ d) d)
```

### Characterization of inequality on the rational numbers by the additive action of `ℚ⁺`

For any `x y : ℚ`, the following conditions are equivalent:

- `x ≤ y`
- `∀ (δ : ℚ⁺) → x < y + δ`
- `∀ (δ : ℚ⁺) → x ≤ y + δ`

```agda
module _
  (x y : ℚ)
  where

  le-add-positive-leq-ℚ :
    (I : leq-ℚ x y) (d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d))
  le-add-positive-leq-ℚ I d =
    concatenate-leq-le-ℚ
      ( x)
      ( y)
      ( y +ℚ (rational-ℚ⁺ d))
      ( I)
      ( le-right-add-rational-ℚ⁺ y d)

  leq-add-positive-le-add-positive-ℚ :
    ((d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d))) →
    ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  leq-add-positive-le-add-positive-ℚ H d =
    leq-le-ℚ
      { x}
      { y +ℚ (rational-ℚ⁺ d)}
      (H d)

  leq-leq-add-positive-ℚ :
    ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d))) → leq-ℚ x y
  leq-leq-add-positive-ℚ H =
    rec-coproduct
      ( λ I →
        ex-falso
          ( not-leq-le-ℚ
            ( mediant-ℚ y x)
            ( x)
            ( le-right-mediant-ℚ y x I)
            ( tr
              ( leq-ℚ x)
              ( right-law-positive-diff-le-ℚ
                ( y)
                ( mediant-ℚ y x)
                ( le-left-mediant-ℚ y x I))
              ( H
                ( positive-diff-le-ℚ
                  ( y)
                  ( mediant-ℚ y x)
                  ( le-left-mediant-ℚ y x I))))))
      ( id)
      ( decide-le-leq-ℚ y x)

  equiv-leq-le-add-positive-ℚ :
    leq-ℚ x y ≃ ((d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  equiv-leq-le-add-positive-ℚ =
    equiv-iff
      ( leq-ℚ-Prop x y)
      ( Π-Prop ℚ⁺ (λ d → le-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d))))
      ( le-add-positive-leq-ℚ)
      ( leq-leq-add-positive-ℚ ∘ leq-add-positive-le-add-positive-ℚ)

  equiv-leq-leq-add-positive-ℚ :
    leq-ℚ x y ≃ ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  equiv-leq-leq-add-positive-ℚ =
    equiv-iff
      ( leq-ℚ-Prop x y)
      ( Π-Prop ℚ⁺ (λ d → leq-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d))))
      ( leq-add-positive-le-add-positive-ℚ ∘ le-add-positive-leq-ℚ)
      ( leq-leq-add-positive-ℚ)
```

```agda
module _
  (x y : ℚ) (d : ℚ⁺)
  where

  le-le-add-positive-leq-add-positive-ℚ :
    (L : leq-ℚ y (x +ℚ (rational-ℚ⁺ d)))
    (r : ℚ)
    (I : le-ℚ (r +ℚ rational-ℚ⁺ d) y) →
    le-ℚ r x
  le-le-add-positive-leq-add-positive-ℚ L r I =
    reflects-le-left-add-ℚ
      ( rational-ℚ⁺ d)
      ( r)
      ( x)
      ( concatenate-le-leq-ℚ
        ( r +ℚ rational-ℚ⁺ d)
        ( y)
        ( x +ℚ rational-ℚ⁺ d)
        ( I)
        ( L))

  leq-add-positive-le-le-add-positive-ℚ :
    ((r : ℚ) → le-ℚ (r +ℚ rational-ℚ⁺ d) y → le-ℚ r x) →
    leq-ℚ y (x +ℚ rational-ℚ⁺ d)
  leq-add-positive-le-le-add-positive-ℚ L =
    rec-coproduct
      ( ex-falso ∘ (irreflexive-le-ℚ x) ∘ L x)
      ( id)
      ( decide-le-leq-ℚ (x +ℚ rational-ℚ⁺ d) y)
```
