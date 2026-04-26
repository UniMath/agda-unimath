# Addition of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.addition-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.semigroups
open import group-theory.subsemigroups
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of two positive rational numbers" Agda=add-ℚ⁺}}
of two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is their [sum](elementary-number-theory.addition-rational-numbers.md) as
[rational numbers](elementary-number-theory.rational-numbers.md), and is itself
positive.

## Definition

### The sum of two positive rational numbers is positive

```agda
opaque
  unfolding add-ℚ is-positive-ℚ

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

## Properties

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

### Addition with a positive rational number is a strictly increasing map

```agda
abstract
  le-left-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ x ((rational-ℚ⁺ d) +ℚ x)
  le-left-add-rational-ℚ⁺ x d =
    concatenate-leq-le-ℚ
      ( x)
      ( zero-ℚ +ℚ x)
      ( (rational-ℚ⁺ d) +ℚ x)
      ( inv-tr (leq-ℚ x) (left-unit-law-add-ℚ x) (refl-leq-ℚ x))
      ( preserves-strict-order-left-add-ℚ
        ( x)
        ( zero-ℚ)
        ( rational-ℚ⁺ d)
        ( le-zero-is-positive-ℚ (is-positive-rational-ℚ⁺ d)))

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

### The sum of two positive rational numbers is greater than each of them

```agda
module _
  (x y : ℚ⁺)
  where

  abstract
    le-left-add-ℚ⁺ : le-ℚ⁺ x (x +ℚ⁺ y)
    le-left-add-ℚ⁺ =
      tr
        ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
        ( right-unit-law-add-ℚ (rational-ℚ⁺ x))
        ( preserves-strict-order-right-add-ℚ
          ( rational-ℚ⁺ x)
          ( zero-ℚ)
          ( rational-ℚ⁺ y)
          ( le-zero-is-positive-ℚ (is-positive-rational-ℚ⁺ y)))

    le-right-add-ℚ⁺ : le-ℚ⁺ y (x +ℚ⁺ y)
    le-right-add-ℚ⁺ =
      tr
        ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
        ( left-unit-law-add-ℚ (rational-ℚ⁺ y))
        ( preserves-strict-order-left-add-ℚ
          ( rational-ℚ⁺ y)
          ( zero-ℚ)
          ( rational-ℚ⁺ x)
          ( le-zero-is-positive-ℚ (is-positive-rational-ℚ⁺ x)))
```

### The positive difference of strictly inequal positive rational numbers

```agda
module _
  (x y : ℚ⁺) (H : le-ℚ⁺ x y)
  where

  le-diff-ℚ⁺ : ℚ⁺
  le-diff-ℚ⁺ = positive-diff-le-ℚ H

  abstract
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

### Any positive rational number can be expressed as the sum of two positive rational numbers

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
    ( left-summand-split-ℚ⁺ ,
      right-summand-split-ℚ⁺ ,
      eq-add-split-ℚ⁺)

  abstract
    le-left-summand-split-ℚ⁺ : le-ℚ⁺ left-summand-split-ℚ⁺ x
    le-left-summand-split-ℚ⁺ = le-mediant-zero-ℚ⁺ x

    leq-left-summand-split-ℚ⁺ : leq-ℚ⁺ left-summand-split-ℚ⁺ x
    leq-left-summand-split-ℚ⁺ = leq-le-ℚ le-left-summand-split-ℚ⁺

    le-right-summand-split-ℚ⁺ : le-ℚ⁺ right-summand-split-ℚ⁺ x
    le-right-summand-split-ℚ⁺ =
      tr
        ( le-ℚ⁺ right-summand-split-ℚ⁺)
        ( eq-add-split-ℚ⁺)
        ( le-right-add-ℚ⁺ left-summand-split-ℚ⁺ right-summand-split-ℚ⁺)

    leq-right-summand-split-ℚ⁺ : leq-ℚ⁺ right-summand-split-ℚ⁺ x
    leq-right-summand-split-ℚ⁺ = leq-le-ℚ le-right-summand-split-ℚ⁺

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
        ( preserves-strict-order-add-ℚ
          { p}
          { q +ℚ rational-ℚ⁺ left-summand-split-ℚ⁺}
          { r}
          { s +ℚ rational-ℚ⁺ right-summand-split-ℚ⁺}
          ( p<q+left)
          ( r<s+right))
```

### Any positive rational number can be expressed as the sum of three positive rational numbers

```agda
module _
  (x : ℚ⁺)
  where

  left-summand-split-ternary-ℚ⁺ : ℚ⁺
  left-summand-split-ternary-ℚ⁺ = left-summand-split-ℚ⁺ x

  middle-summand-split-ternary-ℚ⁺ : ℚ⁺
  middle-summand-split-ternary-ℚ⁺ =
    left-summand-split-ℚ⁺ (right-summand-split-ℚ⁺ x)

  right-summand-split-ternary-ℚ⁺ : ℚ⁺
  right-summand-split-ternary-ℚ⁺ =
    right-summand-split-ℚ⁺ (right-summand-split-ℚ⁺ x)

  eq-add-split-ternary-ℚ⁺ :
    ( ( left-summand-split-ternary-ℚ⁺ +ℚ⁺
        middle-summand-split-ternary-ℚ⁺) +ℚ⁺
      ( right-summand-split-ternary-ℚ⁺)) ＝
    ( x)
  eq-add-split-ternary-ℚ⁺ =
    ( associative-add-ℚ⁺
      ( left-summand-split-ternary-ℚ⁺)
      ( middle-summand-split-ternary-ℚ⁺)
      ( right-summand-split-ternary-ℚ⁺)) ∙
    ( ap
      ( left-summand-split-ternary-ℚ⁺ +ℚ⁺_)
      ( eq-add-split-ℚ⁺ (right-summand-split-ℚ⁺ x))) ∙
    ( eq-add-split-ℚ⁺ x)

  split-ternary-ℚ⁺ :
    Σ ℚ⁺ (λ u → Σ ℚ⁺ (λ v → Σ ℚ⁺ (λ w → (u +ℚ⁺ v) +ℚ⁺ w ＝ x)))
  split-ternary-ℚ⁺ =
    ( left-summand-split-ternary-ℚ⁺ ,
      middle-summand-split-ternary-ℚ⁺ ,
      right-summand-split-ternary-ℚ⁺ ,
      eq-add-split-ternary-ℚ⁺)
```

### Subtraction by a positive rational number is a strictly deflationary map

```agda
abstract
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

  abstract
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
        ( λ y<x →
          ex-falso
            ( not-leq-le-ℚ
              ( mediant-ℚ y x)
              ( x)
              ( le-right-mediant-ℚ y<x)
              ( tr
                ( leq-ℚ x)
                ( right-law-positive-diff-le-ℚ (le-left-mediant-ℚ y<x))
                ( H (positive-diff-le-ℚ (le-left-mediant-ℚ y<x))))))
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

  abstract
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
        ( preserves-strict-order-add-ℚ
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

  abstract
    double-le-ℚ⁺ : exists ℚ⁺ (λ q → le-prop-ℚ⁺ (q +ℚ⁺ q) p)
    double-le-ℚ⁺ = unit-trunc-Prop bound-double-le-ℚ⁺
```
