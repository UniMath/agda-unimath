# Relatively prime natural numbers

```agda
module elementary-number-theory.relatively-prime-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Two natural numbers `x` and `y` are said to be relatively prime if their
greatest common divisor is `1`.

## Definition

```agda
relatively-prime-ℕ : ℕ → ℕ → UU lzero
relatively-prime-ℕ x y = is-one-ℕ (gcd-ℕ x y)
```

## Properties

### Being relatively prime is a proposition

```agda
is-prop-relatively-prime-ℕ : (x y : ℕ) → is-prop (relatively-prime-ℕ x y)
is-prop-relatively-prime-ℕ x y = is-set-ℕ (gcd-ℕ x y) 1

relatively-prime-ℕ-Prop : ℕ → ℕ → Prop lzero
pr1 (relatively-prime-ℕ-Prop x y) = relatively-prime-ℕ x y
pr2 (relatively-prime-ℕ-Prop x y) = is-prop-relatively-prime-ℕ x y
```

### Being relatively prime is decidable

```agda
is-decidable-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable (relatively-prime-ℕ x y)
is-decidable-relatively-prime-ℕ x y = is-decidable-is-one-ℕ (gcd-ℕ x y)

is-decidable-prop-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable-prop (relatively-prime-ℕ x y)
pr1 (is-decidable-prop-relatively-prime-ℕ x y) =
  is-prop-relatively-prime-ℕ x y
pr2 (is-decidable-prop-relatively-prime-ℕ x y) =
  is-decidable-relatively-prime-ℕ x y
```

### For any two natural numbers `a` and `b` such that `a + b ≠ 0`, the numbers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
relatively-prime-quotient-div-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (add-ℕ a b) →
  relatively-prime-ℕ
    ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
    ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b))
relatively-prime-quotient-div-gcd-ℕ a b nz =
  ( uniqueness-is-gcd-ℕ
    ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
    ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b))
    ( gcd-ℕ
      ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
      ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b)))
    ( quotient-div-ℕ
      ( gcd-ℕ a b)
      ( gcd-ℕ a b)
      ( div-gcd-is-common-divisor-ℕ a b
        ( gcd-ℕ a b)
        ( is-common-divisor-gcd-ℕ a b)))
    ( is-gcd-gcd-ℕ
      ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
      ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b)))
    ( is-gcd-quotient-div-gcd-ℕ
      ( is-nonzero-gcd-ℕ a b nz)
      ( is-common-divisor-gcd-ℕ a b ))) ∙
  ( is-idempotent-quotient-div-ℕ
    ( gcd-ℕ a b)
    ( is-nonzero-gcd-ℕ a b nz)
    ( div-gcd-is-common-divisor-ℕ a b
      ( gcd-ℕ a b)
      ( is-common-divisor-gcd-ℕ a b)))
```
