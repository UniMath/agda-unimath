# Unit fractions in the rational numbers types

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.unit-fractions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-positive-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes

open import group-theory.groups
```

</details>

## Idea

The {{#concept "unit fractions" WDID=Q255388 WD="unit fraction"}} are
[rational numbers](elementary-number-theory.rational-numbers.md) whose numerator
is 1 and whose denominator is a positive integer (or, equivalently, a positive
natural number).

## Definitions

### Reciprocals of nonzero natural numbers

```agda
positive-reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ⁺
positive-reciprocal-rational-ℕ⁺ n = inv-ℚ⁺ (positive-rational-ℕ⁺ n)

reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ
reciprocal-rational-ℕ⁺ n = rational-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n)

positive-reciprocal-rational-succ-ℕ : ℕ → ℚ⁺
positive-reciprocal-rational-succ-ℕ n =
  positive-reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n)

reciprocal-rational-succ-ℕ : ℕ → ℚ
reciprocal-rational-succ-ℕ n =
  reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n)
```

### Reciprocals of positive integers

```agda
positive-reciprocal-rational-ℤ⁺ : ℤ⁺ → ℚ⁺
positive-reciprocal-rational-ℤ⁺ k =
  positive-reciprocal-rational-ℕ⁺ (positive-nat-ℤ⁺ k)

reciprocal-rational-ℤ⁺ : ℤ⁺ → ℚ
reciprocal-rational-ℤ⁺ k =
  reciprocal-rational-ℕ⁺ (positive-nat-ℤ⁺ k)
```

## Properties

### The numerator of a unit fraction is one

```agda
abstract
  eq-numerator-reciprocal-rational-ℤ⁺ :
    (k : ℤ⁺) → numerator-ℚ (reciprocal-rational-ℤ⁺ k) ＝ one-ℤ
  eq-numerator-reciprocal-rational-ℤ⁺ k =
    eq-numerator-inv-denominator-ℚ⁺
      ( positive-rational-ℕ⁺ (positive-nat-ℤ⁺ k))
```

### The denominator of the reciprocal of `k` is `k`

```agda
module _
  (k : ℤ⁺)
  where

  abstract
    eq-denominator-reciprocal-rational-ℤ⁺ :
      denominator-ℚ (reciprocal-rational-ℤ⁺ k) ＝ int-positive-ℤ k
    eq-denominator-reciprocal-rational-ℤ⁺ =
      ( eq-denominator-inv-numerator-ℚ⁺
        ( positive-rational-ℕ⁺ (positive-nat-ℤ⁺ k))) ∙
      ( ap pr1 (is-section-positive-nat-ℤ⁺ k))

    eq-positive-denominator-reciprocal-rational-ℤ⁺ :
      positive-denominator-ℚ (reciprocal-rational-ℤ⁺ k) ＝ k
    eq-positive-denominator-reciprocal-rational-ℤ⁺ =
      eq-type-subtype
        ( subtype-positive-ℤ)
        ( eq-denominator-reciprocal-rational-ℤ⁺)
```

### If `m ≤ n`, the reciprocal of `n` is less than or equal to the reciprocal of `n`

```agda
abstract
  leq-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → leq-ℕ⁺ m n →
    leq-ℚ (reciprocal-rational-ℕ⁺ n) (reciprocal-rational-ℕ⁺ m)
  leq-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m≤n =
    binary-tr
      ( leq-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( leq-int-ℕ m n m≤n)
```

### If `m < n`, the reciprocal of `n` is less than the reciprocal of `n`

```agda
abstract
  le-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → le-ℕ⁺ m n →
    le-ℚ⁺
      ( positive-reciprocal-rational-ℕ⁺ n)
      ( positive-reciprocal-rational-ℕ⁺ m)
  le-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m<n =
    binary-tr
      ( le-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( le-natural-le-ℤ m n m<n)
```

### For every positive rational number, there is a smaller unit fraction

```agda
smaller-reciprocal-ℚ⁺ :
  (q : ℚ⁺) → Σ ℕ⁺ (λ n → le-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n) q)
smaller-reciprocal-ℚ⁺ q⁺@(q , _) =
  tot
    ( λ n⁺ 1<nq →
      binary-tr
        ( le-ℚ)
        ( right-unit-law-mul-ℚ _)
        ( ap
          ( rational-ℚ⁺)
          ( is-retraction-left-div-Group
            ( group-mul-ℚ⁺)
            ( positive-rational-ℕ⁺ n⁺)
            ( q⁺)))
        ( preserves-le-left-mul-ℚ⁺
          ( positive-reciprocal-rational-ℕ⁺ n⁺)
          ( one-ℚ)
          ( rational-ℚ⁺ (positive-rational-ℕ⁺ n⁺ *ℚ⁺ q⁺))
          ( 1<nq)))
    ( bound-archimedean-property-ℚ⁺ q⁺ one-ℚ⁺)
```

### The reciprocal of `n : ℕ⁺` is a multiplicative inverse of `n`

```agda
module _
  (n : ℕ⁺)
  where

  abstract
    left-inverse-law-positive-reciprocal-rational-ℕ⁺ :
      mul-ℚ⁺
        ( positive-reciprocal-rational-ℕ⁺ n)
        ( positive-rational-ℕ⁺ n) ＝
      one-ℚ⁺
    left-inverse-law-positive-reciprocal-rational-ℕ⁺ =
      left-inverse-law-mul-ℚ⁺ (positive-rational-ℕ⁺ n)

    left-inverse-law-reciprocal-rational-ℕ⁺ :
      mul-ℚ
        ( reciprocal-rational-ℕ⁺ n)
        ( rational-ℚ⁺ (positive-rational-ℕ⁺ n)) ＝
      one-ℚ
    left-inverse-law-reciprocal-rational-ℕ⁺ =
      ap rational-ℚ⁺ left-inverse-law-positive-reciprocal-rational-ℕ⁺

    right-inverse-law-positive-reciprocal-rational-ℕ⁺ :
      mul-ℚ⁺
        ( positive-rational-ℕ⁺ n)
        ( positive-reciprocal-rational-ℕ⁺ n) ＝
      one-ℚ⁺
    right-inverse-law-positive-reciprocal-rational-ℕ⁺ =
      right-inverse-law-mul-ℚ⁺ (positive-rational-ℕ⁺ n)

    right-inverse-law-reciprocal-rational-ℕ⁺ :
      mul-ℚ
        ( rational-ℚ⁺ (positive-rational-ℕ⁺ n))
        ( reciprocal-rational-ℕ⁺ n) ＝
      one-ℚ
    right-inverse-law-reciprocal-rational-ℕ⁺ =
      ap rational-ℚ⁺ right-inverse-law-positive-reciprocal-rational-ℕ⁺
```

### The reciprocal of `k : ℤ⁺` is a multiplicative inverse of `k`

```agda
module _
  (k : ℤ⁺)
  where

  abstract
    left-inverse-law-positive-reciprocal-rational-ℤ⁺ :
      mul-ℚ⁺
        ( positive-reciprocal-rational-ℤ⁺ k)
        ( positive-rational-ℤ⁺ k) ＝
      one-ℚ⁺
    left-inverse-law-positive-reciprocal-rational-ℤ⁺ =
      binary-tr
        ( λ u v → u *ℚ⁺ v ＝ one-ℚ⁺)
        ( refl)
        ( ap positive-rational-ℤ⁺ (is-section-positive-nat-ℤ⁺ k))
        ( left-inverse-law-positive-reciprocal-rational-ℕ⁺
          ( positive-nat-ℤ⁺ k))

    left-inverse-law-reciprocal-rational-ℤ⁺ :
      mul-ℚ
        ( reciprocal-rational-ℤ⁺ k)
        ( rational-ℚ⁺ (positive-rational-ℤ⁺ k)) ＝
      one-ℚ
    left-inverse-law-reciprocal-rational-ℤ⁺ =
      ap rational-ℚ⁺ left-inverse-law-positive-reciprocal-rational-ℤ⁺

    right-inverse-law-positive-reciprocal-rational-ℤ⁺ :
      mul-ℚ⁺
        ( positive-rational-ℤ⁺ k)
        ( positive-reciprocal-rational-ℤ⁺ k) ＝
      one-ℚ⁺
    right-inverse-law-positive-reciprocal-rational-ℤ⁺ =
      binary-tr
        ( λ u v → u *ℚ⁺ v ＝ one-ℚ⁺)
        ( ap positive-rational-ℤ⁺ (is-section-positive-nat-ℤ⁺ k))
        ( refl)
        ( right-inverse-law-positive-reciprocal-rational-ℕ⁺
          ( positive-nat-ℤ⁺ k))

    right-inverse-law-reciprocal-rational-ℤ⁺ :
      mul-ℚ
        ( rational-ℚ⁺ (positive-rational-ℤ⁺ k))
        ( reciprocal-rational-ℤ⁺ k) ＝
      one-ℚ
    right-inverse-law-reciprocal-rational-ℤ⁺ =
      ap rational-ℚ⁺ right-inverse-law-positive-reciprocal-rational-ℤ⁺
```

### Any rational number is the product of its numerator and the reciprocal of its denominator

```agda
module _
  (x : ℚ)
  where

  abstract
    eq-mul-numerator-reciprocal-denominator-ℚ :
      mul-ℚ
        ( rational-ℤ (numerator-ℚ x))
        ( reciprocal-rational-ℤ⁺ (positive-denominator-ℚ x)) ＝
      x
    eq-mul-numerator-reciprocal-denominator-ℚ =
      ( ap
        ( mul-ℚ' (reciprocal-rational-ℤ⁺ (positive-denominator-ℚ x)))
        ( inv (eq-numerator-mul-denominator-ℚ x))) ∙
      ( associative-mul-ℚ
        ( x)
        ( rational-ℤ (denominator-ℚ x))
        ( reciprocal-rational-ℤ⁺ (positive-denominator-ℚ x))) ∙
      ( ap
        ( mul-ℚ x)
        ( right-inverse-law-reciprocal-rational-ℤ⁺
          ( positive-denominator-ℚ x))) ∙
      ( right-unit-law-mul-ℚ x)

    eq-mul-numerator-reciprocal-denominator-ℚ' :
      mul-ℚ
        ( reciprocal-rational-ℤ⁺ (positive-denominator-ℚ x))
        ( rational-ℤ (numerator-ℚ x)) ＝
      x
    eq-mul-numerator-reciprocal-denominator-ℚ' =
      ( commutative-mul-ℚ
        ( reciprocal-rational-ℤ⁺ (positive-denominator-ℚ x))
        ( rational-ℤ (numerator-ℚ x))) ∙
      ( eq-mul-numerator-reciprocal-denominator-ℚ)
```
