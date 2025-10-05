# Strict inequality on the integer fractions

```agda
module elementary-number-theory.strict-inequality-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `m/n` is
_strictly less than_ the fraction `m'/n'` if the
[integer product](elementary-number-theory.multiplication-integers.md) `m * n'`
is [strictly less](elementary-number-theory.strict-inequality-integers.md) than
`m' * n`.

## Definition

### Strict inequality on the integer fractions

```agda
le-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
le-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  le-prop-ℤ (m *ℤ n') (m' *ℤ n)

le-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
le-fraction-ℤ x y = type-Prop (le-fraction-ℤ-Prop x y)

is-prop-le-fraction-ℤ : (x y : fraction-ℤ) → is-prop (le-fraction-ℤ x y)
is-prop-le-fraction-ℤ x y = is-prop-type-Prop (le-fraction-ℤ-Prop x y)
```

## Properties

### Strict inequality on the integer fractions is decidable

```agda
is-decidable-le-fraction-ℤ :
  (x y : fraction-ℤ) → (le-fraction-ℤ x y) + ¬ (le-fraction-ℤ x y)
is-decidable-le-fraction-ℤ x y =
  is-decidable-le-ℤ
    ( numerator-fraction-ℤ x *ℤ denominator-fraction-ℤ y)
    ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x)

le-fraction-ℤ-Decidable-Prop : (x y : fraction-ℤ) → Decidable-Prop lzero
le-fraction-ℤ-Decidable-Prop x y =
  ( le-fraction-ℤ x y ,
    is-prop-le-fraction-ℤ x y ,
    is-decidable-le-fraction-ℤ x y)

decide-le-leq-fraction-ℤ :
  (x y : fraction-ℤ) → le-fraction-ℤ x y + leq-fraction-ℤ y x
decide-le-leq-fraction-ℤ x y =
  map-coproduct
    ( id)
    ( λ H →
      is-nonnegative-eq-ℤ
        ( skew-commutative-cross-mul-diff-fraction-ℤ x y)
        ( is-nonnegative-neg-is-nonpositive-ℤ H))
    ( decide-is-positive-is-nonpositive-ℤ)
```

### Strict inequality on the integer fractions implies inequality

```agda
leq-le-fraction-ℤ : {x y : fraction-ℤ} → le-fraction-ℤ x y → leq-fraction-ℤ x y
leq-le-fraction-ℤ {x} {y} =
  leq-le-ℤ
    { mul-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ y)}
    { mul-ℤ (numerator-fraction-ℤ y) (denominator-fraction-ℤ x)}
```

### Strict inequality on the integer fractions is asymmetric

```agda
module _
  (x y : fraction-ℤ)
  where

  asymmetric-le-fraction-ℤ :
    le-fraction-ℤ x y → ¬ (le-fraction-ℤ y x)
  asymmetric-le-fraction-ℤ =
    asymmetric-le-ℤ
      ( mul-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ y))
      ( mul-ℤ
        ( numerator-fraction-ℤ y)
        ( denominator-fraction-ℤ x))
```

### Strict inequality on the integer fractions is transitive

```agda
transitive-le-fraction-ℤ :
  (p q r : fraction-ℤ) →
  le-fraction-ℤ q r →
  le-fraction-ℤ p q →
  le-fraction-ℤ p r
transitive-le-fraction-ℤ p q r H H' =
  is-positive-right-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
      ( is-positive-add-ℤ
        ( is-positive-mul-ℤ
          ( is-positive-denominator-fraction-ℤ p)
          ( H))
        ( is-positive-mul-ℤ
          ( is-positive-denominator-fraction-ℤ r)
          ( H'))))
      ( is-positive-denominator-fraction-ℤ q)
```

### Chaining rules for inequality and strict inequality on the integer fractions

```agda
module _
  (p q r : fraction-ℤ)
  where

  abstract
    concatenate-le-leq-fraction-ℤ :
      le-fraction-ℤ p q →
      leq-fraction-ℤ q r →
      le-fraction-ℤ p r
    concatenate-le-leq-fraction-ℤ H H' =
      is-positive-right-factor-mul-ℤ
        ( is-positive-eq-ℤ
          ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
          ( is-positive-add-nonnegative-positive-ℤ
            ( is-nonnegative-mul-ℤ
              ( is-nonnegative-is-positive-ℤ
                ( is-positive-denominator-fraction-ℤ p))
              ( H'))
            ( is-positive-mul-ℤ
              ( is-positive-denominator-fraction-ℤ r)
              ( H))))
        ( is-positive-denominator-fraction-ℤ q)

    concatenate-leq-le-fraction-ℤ :
      leq-fraction-ℤ p q →
      le-fraction-ℤ q r →
      le-fraction-ℤ p r
    concatenate-leq-le-fraction-ℤ H H' =
      is-positive-right-factor-mul-ℤ
        ( is-positive-eq-ℤ
          ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
          ( is-positive-add-positive-nonnegative-ℤ
            ( is-positive-mul-ℤ
              ( is-positive-denominator-fraction-ℤ p)
              ( H'))
            ( is-nonnegative-mul-ℤ
              ( is-nonnegative-is-positive-ℤ
                ( is-positive-denominator-fraction-ℤ r))
              ( H))))
        ( is-positive-denominator-fraction-ℤ q)
```

### Chaining rules for similarity and strict inequality on the integer fractions

```agda
module _
  (p q r : fraction-ℤ)
  where

  concatenate-sim-le-fraction-ℤ :
    sim-fraction-ℤ p q →
    le-fraction-ℤ q r →
    le-fraction-ℤ p r
  concatenate-sim-le-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( lemma-left-sim-cross-mul-diff-fraction-ℤ p q r H)
        ( is-positive-mul-ℤ
          ( is-positive-denominator-fraction-ℤ p)
          ( H')))
      ( is-positive-denominator-fraction-ℤ q)

  concatenate-le-sim-fraction-ℤ :
    le-fraction-ℤ p q →
    sim-fraction-ℤ q r →
    le-fraction-ℤ p r
  concatenate-le-sim-fraction-ℤ H H' =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( inv ( lemma-right-sim-cross-mul-diff-fraction-ℤ p q r H'))
        ( is-positive-mul-ℤ
          ( is-positive-denominator-fraction-ℤ r)
          ( H)))
      ( is-positive-denominator-fraction-ℤ q)
```

### The similarity of integer fractions preserves strict inequality

```agda
module _
  (p q p' q' : fraction-ℤ) (H : sim-fraction-ℤ p p') (K : sim-fraction-ℤ q q')
  where

  preserves-le-sim-fraction-ℤ : le-fraction-ℤ p q → le-fraction-ℤ p' q'
  preserves-le-sim-fraction-ℤ I =
    concatenate-sim-le-fraction-ℤ p' p q'
      ( symmetric-sim-fraction-ℤ p p' H)
      ( concatenate-le-sim-fraction-ℤ p q q' I K)
```

### Fractions with equal denominator compare the same as their numerators

```agda
module _
  (x y : fraction-ℤ) (H : denominator-fraction-ℤ x ＝ denominator-fraction-ℤ y)
  where

  le-fraction-le-numerator-fraction-ℤ :
    le-ℤ (numerator-fraction-ℤ x) (numerator-fraction-ℤ y) →
    le-fraction-ℤ x y
  le-fraction-le-numerator-fraction-ℤ H' =
    tr
      ( λ (k : ℤ) →
        le-ℤ
          ( numerator-fraction-ℤ x *ℤ k)
          ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x))
      ( H)
      ( preserves-le-left-mul-positive-ℤ
        ( positive-denominator-fraction-ℤ x)
        ( numerator-fraction-ℤ x)
        ( numerator-fraction-ℤ y)
        ( H'))
```

### The mediant of two distinct fractions lies strictly between them

```agda
module _
  (x y : fraction-ℤ)
  where

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

### Strict inequality on the integer fractions is dense

```agda
module _
  (x y : fraction-ℤ) (H : le-fraction-ℤ x y)
  where

  dense-le-fraction-ℤ :
    exists fraction-ℤ (λ r → le-fraction-ℤ-Prop x r ∧ le-fraction-ℤ-Prop r y)
  dense-le-fraction-ℤ =
    intro-exists
      ( mediant-fraction-ℤ x y)
      ( le-left-mediant-fraction-ℤ x y H , le-right-mediant-fraction-ℤ x y H)
```

### Strict inequality on the integer fractions is located

```agda
module _
  (x y z : fraction-ℤ)
  where

  located-le-fraction-ℤ :
    le-fraction-ℤ y z →
    type-disjunction-Prop (le-fraction-ℤ-Prop y x) (le-fraction-ℤ-Prop x z)
  located-le-fraction-ℤ H =
    unit-trunc-Prop
      ( map-coproduct
        ( id)
        ( λ p → concatenate-leq-le-fraction-ℤ x y z p H)
        ( decide-le-leq-fraction-ℤ y x))
```

### `x < y` if and only if `0 < y - x`

```agda
module _
  (x y : fraction-ℤ)
  where

  eq-translate-diff-le-zero-fraction-ℤ :
    le-fraction-ℤ zero-fraction-ℤ (y +fraction-ℤ (neg-fraction-ℤ x)) ＝
    le-fraction-ℤ x y
  eq-translate-diff-le-zero-fraction-ℤ =
    ap
      ( is-positive-ℤ)
      ( ( cross-mul-diff-zero-fraction-ℤ (y +fraction-ℤ (neg-fraction-ℤ x))) ∙
        ( ap
          ( add-ℤ ( (numerator-fraction-ℤ y) *ℤ (denominator-fraction-ℤ x)))
          ( left-negative-law-mul-ℤ
            ( numerator-fraction-ℤ x)
            ( denominator-fraction-ℤ y))))
```

### Negation reverses the order of strict inequality on integer fractions

```agda
neg-le-fraction-ℤ :
  (x y : fraction-ℤ) →
  le-fraction-ℤ x y →
  le-fraction-ℤ (neg-fraction-ℤ y) (neg-fraction-ℤ x)
neg-le-fraction-ℤ (m , n , p) (m' , n' , p') H =
  binary-tr le-ℤ
    ( inv (left-negative-law-mul-ℤ m' n))
    ( inv (left-negative-law-mul-ℤ m n'))
    ( neg-le-ℤ (m *ℤ n') (m' *ℤ n) H)
```
