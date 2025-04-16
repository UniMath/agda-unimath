# The natural part of a positive rational number

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.natural-part-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.archimedean-property-natural-numbers
open import elementary-number-theory.archimedean-property-positive-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The
{{concept "natural part" Disambiguation="positive rational number" Agda=nat-part-ℚ⁺}}
of a
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`x : ℚ⁺` is the unique [natural](elementary-number-theory.natural-numbers.md)
`n : ℕ` such that `n ≤ x < n + 1`. It can be computed as the
[Archimedean modulus](elementary-number-theory.archimedean-property-positive-integers.md)
of its numerator with respect to its denominator.

## Definition

```agda
module _
  (x : ℚ⁺)
  where

  is-natural-part-prop-ℚ⁺ : ℕ → Prop lzero
  is-natural-part-prop-ℚ⁺ n =
    product-Prop
      ( leq-ℚ-Prop (rational-ℤ (int-ℕ n)) (rational-ℚ⁺ x))
      ( le-ℚ-Prop (rational-ℚ⁺ x) (rational-ℤ (int-ℕ (succ-ℕ n))))

  is-natural-part-ℚ⁺ : ℕ → UU lzero
  is-natural-part-ℚ⁺ n = type-Prop (is-natural-part-prop-ℚ⁺ n)

  type-natural-part-ℚ⁺ : UU lzero
  type-natural-part-ℚ⁺ = type-subtype is-natural-part-prop-ℚ⁺
```

## Property

### The natural part of a positive rational is the Archimedean modulus of its numerator with respect to its denominator

```agda
module _
  (x : ℚ⁺) (n : ℕ)
  where

  is-natural-part-is-archimedean-modulus-numerator-denominator-ℚ⁺ :
    is-archimedean-modulus-ℤ⁺
      ( positive-denominator-ℚ⁺ x)
      ( positive-numerator-ℚ⁺ x)
      ( n) →
    is-natural-part-ℚ⁺ x n
  is-natural-part-is-archimedean-modulus-numerator-denominator-ℚ⁺ (H , K) =
    ( binary-tr
      ( leq-ℚ)
      ( is-retraction-rational-fraction-ℚ (rational-ℤ (int-ℕ n)))
      ( is-retraction-rational-fraction-ℚ (rational-ℚ⁺ x))
      ( preserves-leq-rational-fraction-ℤ
        ( in-fraction-ℤ (int-ℕ n))
        ( fraction-ℚ (rational-ℚ⁺ x))
        ( inv-tr
          ( leq-ℤ (int-ℕ n *ℤ (denominator-ℚ⁺ x)))
          ( right-unit-law-mul-ℤ (numerator-ℚ⁺ x))
          ( H)))) ,
      ( binary-tr
        ( le-ℚ)
        ( is-retraction-rational-fraction-ℚ (rational-ℚ⁺ x))
        ( is-retraction-rational-fraction-ℚ (rational-ℤ (in-pos-ℤ n)))
        ( preserves-le-rational-fraction-ℤ
          ( fraction-ℚ (rational-ℚ⁺ x))
          ( in-fraction-ℤ (in-pos-ℤ n))
          ( inv-tr
            ( λ k → le-ℤ k (in-pos-ℤ n *ℤ (denominator-ℚ⁺ x)))
            ( right-unit-law-mul-ℤ (numerator-ℚ⁺ x))
            ( K))))

  is-archimedean-modulus-numerator-denominator-is-natural-part-ℚ⁺ :
    is-natural-part-ℚ⁺ x n →
    is-archimedean-modulus-ℤ⁺
      ( positive-denominator-ℚ⁺ x)
      ( positive-numerator-ℚ⁺ x)
      ( n)
  is-archimedean-modulus-numerator-denominator-is-natural-part-ℚ⁺ (H , K) =
    ( tr
      ( leq-ℤ (int-ℕ n *ℤ int-positive-ℤ (positive-denominator-ℚ⁺ x)))
      ( right-unit-law-mul-ℤ (numerator-ℚ⁺ x))
      ( H)) ,
    ( tr
      ( λ k → le-ℤ k (in-pos-ℤ n *ℤ (denominator-ℚ⁺ x)))
      ( right-unit-law-mul-ℤ (numerator-ℚ⁺ x))
      ( K))
```

### The natural part of a positive rational number exists and is unique

```agda
module _
  (x : ℚ⁺)
  where

  all-eq-is-natural-part-ℚ⁺ :
    (m n : ℕ) →
    is-natural-part-ℚ⁺ x m →
    is-natural-part-ℚ⁺ x n →
    m ＝ n
  all-eq-is-natural-part-ℚ⁺ m n Hm Hn =
    all-eq-is-archimedean-modulus-ℤ⁺
      ( positive-denominator-ℚ⁺ x)
      ( positive-numerator-ℚ⁺ x)
      ( m)
      ( n)
      ( is-archimedean-modulus-numerator-denominator-is-natural-part-ℚ⁺
        ( x)
        ( m)
        ( Hm))
      ( is-archimedean-modulus-numerator-denominator-is-natural-part-ℚ⁺
        ( x)
        ( n)
        ( Hn))

  is-prop-natural-part-ℚ⁺ : is-prop (type-natural-part-ℚ⁺ x)
  is-prop-natural-part-ℚ⁺ =
    is-prop-all-elements-equal
      ( λ u v →
        eq-type-subtype
          ( is-natural-part-prop-ℚ⁺ x)
          ( all-eq-is-natural-part-ℚ⁺ (pr1 u) (pr1 v) (pr2 u) (pr2 v)))

  natural-part-prop-ℚ⁺ : Prop lzero
  natural-part-prop-ℚ⁺ =
    (type-natural-part-ℚ⁺ x , is-prop-natural-part-ℚ⁺)

  torsorial-natural-part-ℚ⁺ :
    is-torsorial (is-natural-part-ℚ⁺ x)
  torsorial-natural-part-ℚ⁺ =
    ( tot
      ( is-natural-part-is-archimedean-modulus-numerator-denominator-ℚ⁺ x)
      ( center-archimedean-modulus-ℤ⁺
        ( positive-denominator-ℚ⁺ x)
        ( positive-numerator-ℚ⁺ x))) ,
    ( λ x → eq-is-prop is-prop-natural-part-ℚ⁺)
```

### The natural part of a positive rational number

```agda
module _
  (x : ℚ⁺)
  where

  center-natural-part-ℚ⁺ : type-natural-part-ℚ⁺ x
  center-natural-part-ℚ⁺ =
    center (torsorial-natural-part-ℚ⁺ x)

  nat-part-ℚ⁺ : ℕ
  nat-part-ℚ⁺ = pr1 center-natural-part-ℚ⁺

  is-natural-part-nat-part-ℚ⁺ : is-natural-part-ℚ⁺ x nat-part-ℚ⁺
  is-natural-part-nat-part-ℚ⁺ = pr2 center-natural-part-ℚ⁺

  leq-left-nat-part-ℚ⁺ :
    leq-ℚ (rational-ℤ (int-ℕ nat-part-ℚ⁺)) (rational-ℚ⁺ x)
  leq-left-nat-part-ℚ⁺ = pr1 is-natural-part-nat-part-ℚ⁺

  le-right-nat-part-ℚ⁺ :
    le-ℚ (rational-ℚ⁺ x) (rational-ℤ (int-ℕ (succ-ℕ (nat-part-ℚ⁺))))
  le-right-nat-part-ℚ⁺ = pr2 is-natural-part-nat-part-ℚ⁺
```
