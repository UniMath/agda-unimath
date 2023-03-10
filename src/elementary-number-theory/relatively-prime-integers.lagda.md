# Relatively prime integers

```agda
module elementary-number-theory.relatively-prime-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers

open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Two integers are said to be relatively prime if their greatest common divisor is 1.

## Definition

```agda
is-relative-prime-ℤ : ℤ → ℤ → UU lzero
is-relative-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)
```

## Properties

```agda
is-prop-is-relative-prime-ℤ : (x y : ℤ) → is-prop (is-relative-prime-ℤ x y)
is-prop-is-relative-prime-ℤ x y = is-set-ℤ (gcd-ℤ x y) one-ℤ
```
