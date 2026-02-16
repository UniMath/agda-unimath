# Relatively prime integers

```agda
module elementary-number-theory.relatively-prime-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.relatively-prime-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Two [integers](elementary-number-theory.integers.md) `x` and `y` are said to be
{{#concept "relatively prime" Disambiguation="integers" WDID=Q104752 WD="coprime" Agda=is-relatively-prime-ℤ}},
or **coprime**, if their
[greatest common divisor](elementary-number-theory.greatest-common-divisor-integers.md)
is `1`.

## Definition

```agda
is-relatively-prime-ℤ : ℤ → ℤ → UU lzero
is-relatively-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)
```

## Properties

### Being relatively prime is a proposition

```agda
abstract
  is-prop-is-relatively-prime-ℤ :
    (x y : ℤ) → is-prop (is-relatively-prime-ℤ x y)
  is-prop-is-relatively-prime-ℤ x y = is-set-ℤ (gcd-ℤ x y) one-ℤ
```

### Two integers are relatively prime if and only if their absolute values are relatively prime natural numbers

```agda
abstract
  is-relatively-prime-abs-is-relatively-prime-ℤ :
    {a b : ℤ} → is-relatively-prime-ℤ a b →
    is-relatively-prime-ℕ (abs-ℤ a) (abs-ℤ b)
  is-relatively-prime-abs-is-relatively-prime-ℤ {a} {b} H = is-injective-int-ℕ H

  is-relatively-prime-is-relatively-prime-abs-ℤ :
    {a b : ℤ} → is-relatively-prime-ℕ (abs-ℤ a) (abs-ℤ b) →
    is-relatively-prime-ℤ a b
  is-relatively-prime-is-relatively-prime-abs-ℤ {a} {b} H = ap int-ℕ H
```

### For two relatively prime integers `x` and `y` and any integer `d`, if `d` divides `x` and `y`, `d` is a unit

```agda
abstract
  is-unit-div-relatively-prime-ℤ :
    (x y : ℤ) (d : ℤ) → is-relatively-prime-ℤ x y →
    is-common-divisor-ℤ x y d → is-unit-ℤ d
  is-unit-div-relatively-prime-ℤ x y d gcd=1 d|x∧d|y =
    tr
      ( λ k → div-ℤ d k)
      ( gcd=1)
      ( forward-implication (pr2 (is-gcd-gcd-ℤ x y) d) d|x∧d|y)
```

### For any two integers `a` and `b` that are not both `0`, the integers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
{-
relatively-prime-quotient-div-ℤ :
  {a b : ℤ} → (is-nonzero-ℤ a + is-nonzero-ℤ b) →
  is-relatively-prime-ℤ
    ( quotient-div-ℤ (gcd-ℤ a b) a (div-left-gcd-ℤ a b))
    ( quotient-div-ℤ (gcd-ℤ a b) b (div-right-gcd-ℤ a b))
relatively-prime-quotient-div-ℤ H =
  is-relatively-prime-is-relatively-prime-abs-ℤ
    {!!}
-}
```
