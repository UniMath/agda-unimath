# Inequality on integer fractions

```agda
module elementary-number-theory.inequality-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.cross-mul-diff-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A fraction `m/n` is less (or equal) to a fraction `m'/n'` iff `m * n'` is less
(or equal) to `m' * n`.

## Definition

### Inequality of integer fractions

```agda
leq-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
leq-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  leq-ℤ-Prop (m *ℤ n') (m' *ℤ n)

leq-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
leq-fraction-ℤ x y = type-Prop (leq-fraction-ℤ-Prop x y)

is-prop-leq-fraction-ℤ : (x y : fraction-ℤ) → is-prop (leq-fraction-ℤ x y)
is-prop-leq-fraction-ℤ x y = is-prop-type-Prop (leq-fraction-ℤ-Prop x y)
```

### Strict inequality of integer fractions

```agda
le-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
le-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  le-ℤ-Prop (m *ℤ n') (m' *ℤ n)

le-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
le-fraction-ℤ x y = type-Prop (le-fraction-ℤ-Prop x y)

is-prop-le-fraction-ℤ : (x y : fraction-ℤ) → is-prop (le-fraction-ℤ x y)
is-prop-le-fraction-ℤ x y = is-prop-type-Prop (le-fraction-ℤ-Prop x y)
```

## Properties of inequalities of integer fractions

```agda
module _
  (x y : fraction-ℤ)
  where

  is-sim-antisymmetric-leq-fraction-ℤ :
    leq-fraction-ℤ x y →
    leq-fraction-ℤ y x →
    sim-fraction-ℤ x y
  is-sim-antisymmetric-leq-fraction-ℤ H H' =
    sim-is-zero-coss-mul-diff-fraction-ℤ x y
      ( is-zero-is-nonnegative-ℤ
        H
        ( is-nonnegative-eq-ℤ
            ( inv ( neg-cross-mul-diff-fraction-ℤ x y))
            H'))

  is-asymmetric-le-fraction-ℤ :
    le-fraction-ℤ x y → ¬ (le-fraction-ℤ y x)
  is-asymmetric-le-fraction-ℤ =
    is-asymmetric-le-ℤ
      ( mul-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ y))
      ( mul-ℤ
        ( numerator-fraction-ℤ y)
        ( denominator-fraction-ℤ x))
```

### Transitivity properties

```agda
module _
  (p q r : fraction-ℤ)
  where

  transitive-leq-fraction-ℤ :
    leq-fraction-ℤ p q →
    leq-fraction-ℤ q r →
    leq-fraction-ℤ p r
  transitive-leq-fraction-ℤ H H' =
    is-nonnegative-right-factor-mul-ℤ
      ( is-nonnegative-eq-ℤ
        ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
          (is-nonnegative-add-ℤ
            ( denominator-fraction-ℤ p *ℤ cross-mul-diff-fraction-ℤ q r)
            ( denominator-fraction-ℤ r *ℤ cross-mul-diff-fraction-ℤ p q)
            ( is-nonnegative-mul-ℤ
              ( is-nonnegative-is-positive-ℤ
                ( is-positive-denominator-fraction-ℤ p))
              H')
            ( is-nonnegative-mul-ℤ
              ( is-nonnegative-is-positive-ℤ
                ( is-positive-denominator-fraction-ℤ r))
              H)))
      ( is-positive-denominator-fraction-ℤ q)

  transitive-le-fraction-ℤ :
    le-fraction-ℤ p q →
    le-fraction-ℤ q r →
    le-fraction-ℤ p r
  transitive-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
        ( is-positive-add-ℤ
          ( is-positive-mul-ℤ
            ( is-positive-denominator-fraction-ℤ p)
            H')
          ( is-positive-mul-ℤ
            ( is-positive-denominator-fraction-ℤ r)
            H)))
        ( is-positive-denominator-fraction-ℤ q)

  le-leq-le-fraction-ℤ :
    le-fraction-ℤ p q →
    leq-fraction-ℤ q r →
    le-fraction-ℤ p r
  le-leq-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
        ( is-positive-add-nonnegative-positive-ℤ
          ( is-nonnegative-mul-ℤ
            ( is-nonnegative-is-positive-ℤ
              ( is-positive-denominator-fraction-ℤ p))
            H')
          ( is-positive-mul-ℤ
            ( is-positive-denominator-fraction-ℤ r)
            H)))
      ( is-positive-denominator-fraction-ℤ q)

  leq-le-le-fraction-ℤ :
    leq-fraction-ℤ p q →
    le-fraction-ℤ q r →
    le-fraction-ℤ p r
  leq-le-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
        ( is-positive-add-positive-nonnegative-ℤ
          ( is-positive-mul-ℤ
            ( is-positive-denominator-fraction-ℤ p)
            H')
          ( is-nonnegative-mul-ℤ
            ( is-nonnegative-is-positive-ℤ
              ( is-positive-denominator-fraction-ℤ r))
            H)))
      ( is-positive-denominator-fraction-ℤ q)

  sim-le-le-fraction-ℤ :
    sim-fraction-ℤ p q →
    le-fraction-ℤ q r →
    le-fraction-ℤ p r
  sim-le-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( lemma-left-sim-cross-mul-diff-fraction-ℤ p q r H)
        ( is-positive-mul-ℤ
          ( is-positive-denominator-fraction-ℤ p) H'))
      ( is-positive-denominator-fraction-ℤ q)

  le-sim-le-fraction-ℤ :
    le-fraction-ℤ p q →
    sim-fraction-ℤ q r →
    le-fraction-ℤ p r
  le-sim-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( inv ( lemma-right-sim-cross-mul-diff-fraction-ℤ p q r H'))
        ( is-positive-mul-ℤ (is-positive-denominator-fraction-ℤ r) H))
      ( is-positive-denominator-fraction-ℤ q)
```

### Existence properties

- Fractions with the same denominator compare the same as their numerator;
- The mediant of two fractions lies between them.

```agda
module _
  (x y : fraction-ℤ)
  where

  le-numerator-le-fraction-ℤ :
    denominator-fraction-ℤ x ＝ denominator-fraction-ℤ y →
    le-ℤ (numerator-fraction-ℤ x) (numerator-fraction-ℤ y) →
    le-fraction-ℤ x y
  le-numerator-le-fraction-ℤ H H' =
    tr
      ( λ (k : ℤ) →
        le-ℤ
          ( numerator-fraction-ℤ x *ℤ k)
          ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x))
      ( H)
      ( preserves-strict-order-mul-positive-ℤ'
        { numerator-fraction-ℤ x}
        { numerator-fraction-ℤ y}
        ( denominator-fraction-ℤ x)
        ( is-positive-denominator-fraction-ℤ x)
        ( H'))

  le-left-mediant-fraction-ℤ :
    le-fraction-ℤ x y →
    le-fraction-ℤ x (mediant-fraction-ℤ x y)
  le-left-mediant-fraction-ℤ =
    is-positive-eq-ℤ (cross-mul-diff-left-mediant-fraction-ℤ x y)

  le-right-mediant-fraction-ℤ :
    le-fraction-ℤ x y →
    le-fraction-ℤ (mediant-fraction-ℤ x y) y
  le-right-mediant-fraction-ℤ =
    is-positive-eq-ℤ (cross-mul-diff-right-mediant-fraction-ℤ x y)
```
