# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.cross-mul-diff-integer-fractions
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A rational number `x` is less (or equal) to a rational number `y` if and only if
the underlying fraction of `x` is less (or equal) than the underlying fraction
of `y`.

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Prop : ℚ → ℚ → Prop lzero
leq-ℚ-Prop (x , px) (y , py) = leq-fraction-ℤ-Prop x y

leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ x y = type-Prop (leq-ℚ-Prop x y)

is-prop-leq-ℚ : (x y : ℚ) → is-prop (leq-ℚ x y)
is-prop-leq-ℚ x y = is-prop-type-Prop (leq-ℚ-Prop x y)

infix 30 _≤-ℚ_
_≤-ℚ_ = leq-ℚ
```

### Strict inequality on the rational numbers

```agda
le-ℚ-Prop : ℚ → ℚ → Prop lzero
le-ℚ-Prop (x , px) (y , py) = le-fraction-ℤ-Prop x y

le-ℚ : ℚ → ℚ → UU lzero
le-ℚ x y = type-Prop (le-ℚ-Prop x y)

is-prop-le-ℚ : (x y : ℚ) → is-prop (le-ℚ x y)
is-prop-le-ℚ x y = is-prop-type-Prop (le-ℚ-Prop x y)
```

## Properties of inequalities on the rationals

### Inequality on rational numbers is antisymmetric

```agda
is-reflexive-leq-ℚ : (x : ℚ) → leq-ℚ x x
is-reflexive-leq-ℚ x =
  refl-leq-ℤ
    ( numerator-ℚ x *ℤ denominator-ℚ x)

is-antisymmetric-leq-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℚ y x → x ＝ y
is-antisymmetric-leq-ℚ x y H H' =
  ( inv (in-fraction-fraction-ℚ x)) ∙
  ( eq-ℚ-sim-fractions-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)
    ( is-sim-antisymmetric-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( H)
      ( H'))) ∙
    ( in-fraction-fraction-ℚ y)
```

### Strict inequality on rationals is asymmetric

```agda
is-asymmetric-le-ℚ : (x y : ℚ) → le-ℚ x y → ¬ (le-ℚ y x)
is-asymmetric-le-ℚ x y =
  is-asymmetric-le-fraction-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)

is-irreflexive-le-ℚ : (x : ℚ) → ¬ (le-ℚ x x)
is-irreflexive-le-ℚ =
  is-irreflexive-is-asymmetric le-ℚ is-asymmetric-le-ℚ
```

### Transitivity properties

```agda
module _
  (x y z : ℚ)
  where

  transitive-leq-ℚ : leq-ℚ x y → leq-ℚ y z → leq-ℚ x z
  transitive-leq-ℚ =
    transitive-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  transitive-le-ℚ : le-ℚ x y → le-ℚ y z → le-ℚ x z
  transitive-le-ℚ =
    transitive-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  le-leq-le-ℚ : le-ℚ x y → leq-ℚ y z → le-ℚ x z
  le-leq-le-ℚ =
    le-leq-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  leq-le-le-ℚ : leq-ℚ x y → le-ℚ y z → le-ℚ x z
  leq-le-le-ℚ =
    leq-le-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)
```

### Compatibilty with `fraction-ℚ`

Strict inequality on `ℚ` reflects strict inequality on the underlying fractions.

```agda
module _
  (x : ℚ) (p : fraction-ℤ)
  where

  right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ :
    le-fraction-ℤ (fraction-ℚ x) p →
    le-ℚ x (in-fraction-ℤ p)
  right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ H =
    le-sim-le-fraction-ℤ
      ( fraction-ℚ x)
      p
      ( fraction-ℚ ( in-fraction-ℤ p))
      H
      ( sim-reduced-fraction-ℤ p)

  left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ :
    le-fraction-ℤ p (fraction-ℚ x) →
    le-ℚ (in-fraction-ℤ p) x
  left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ =
    sim-le-le-fraction-ℤ
      ( fraction-ℚ ( in-fraction-ℤ p))
      p
      ( fraction-ℚ x)
      ( symmetric-sim-fraction-ℤ
        p
        ( fraction-ℚ ( in-fraction-ℤ p))
        ( sim-reduced-fraction-ℤ p))
```

### Existence properties

```agda
module _
  (x : ℚ)
  where

  left-∃-le-ℚ : ∃ ℚ (λ q → le-ℚ q x)
  left-∃-le-ℚ = intro-∃
    ( in-fraction-ℤ frac)
    ( left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x frac
      ( le-numerator-le-fraction-ℤ
        frac
        ( fraction-ℚ x)
        refl
        ( le-pred-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = (pred-ℤ (numerator-ℚ x) , positive-denominator-ℚ x)

  right-∃-le-ℚ : ∃ ℚ (λ r → le-ℚ x r)
  right-∃-le-ℚ = intro-∃
    ( in-fraction-ℤ frac)
    ( right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x frac
      ( le-numerator-le-fraction-ℤ
        ( fraction-ℚ x)
        frac
        refl
        ( le-succ-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = (succ-ℤ (numerator-ℚ x) , positive-denominator-ℚ x)
```

Decidability and trichotomy properties

```agda
decide-le-leq-ℚ : (x y : ℚ) → le-ℚ x y + leq-ℚ y x
decide-le-leq-ℚ x y =
  map-coproduct
    ( id)
    ( is-nonnegative-eq-ℤ
      ( neg-cross-mul-diff-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)))
    ( decide-is-positive-ℤ
      { cross-mul-diff-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)})

trichotomy-le-ℚ :
  {l : Level} {A : UU l} (x y : ℚ) →
  ( le-ℚ x y → A) →
  ( Id x y → A) →
  ( le-ℚ y x → A) →
  A
trichotomy-le-ℚ x y left eq right =
  rec-coproduct
    right
    ( λ I →
      rec-coproduct
        left
        ( eq ∘ is-antisymmetric-leq-ℚ x y I)
        ( decide-le-leq-ℚ x y))
    ( decide-le-leq-ℚ y x)
```

### The mediant of two rationals is between them

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  le-left-mediant-ℚ : le-ℚ x (mediant-ℚ x y)
  le-left-mediant-ℚ =
    right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-left-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)

  le-right-mediant-ℚ : le-ℚ (mediant-ℚ x y) y
  le-right-mediant-ℚ =
    left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ y
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-right-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)
```

### Strict inequality on the rationals is dense

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  dense-le-ℚ : ∃ ℚ (λ r → le-ℚ x r × le-ℚ r y)
  dense-le-ℚ =
    intro-∃
      ( mediant-ℚ x y)
      ( le-left-mediant-ℚ x y H , le-right-mediant-ℚ x y H)
```

### The strict order on the rationals is located

```agda
is-located-le-ℚ : (x y z : ℚ) → le-ℚ y z → le-ℚ y x + le-ℚ x z
is-located-le-ℚ x y z H =
  map-coproduct
    id
    ( λ p → leq-le-le-ℚ x y z p H)
    ( decide-le-leq-ℚ y x)
```
