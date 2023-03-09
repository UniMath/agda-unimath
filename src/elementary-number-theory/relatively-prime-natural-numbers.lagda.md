# Relatively prime natural numbers

```agda
module elementary-number-theory.relatively-prime-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Two natural numbers `x` and `y` are said to be relatively prime if their greatest common divisor is `1`.

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

### A number y is relatively prime to x if and only if `[y] mod x` is a unit in `ℤ-Mod x`

```agda
-- relatively-prime-is-unit-mod-ℕ :
--   (x y : ℕ) → is-unit-ℤ-Mod x (mod-ℕ y) → relatively-prime-ℕ x y
-- relatively-prime-is-unit-mod-ℕ x y H = ?
