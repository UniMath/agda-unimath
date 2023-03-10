# Proper divisors of natural numbers

```agda
module elementary-number-theory.proper-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

 A proper divisor of a natural number `n` is a natural number `d ≠ n` that divides `n`.

```agda
is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = ¬ (d ＝ n) × div-ℕ d n

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = is-nonzero-succ-ℕ n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)
```

## Properties

### Being a proper divisor is a property

```agda
is-prop-is-proper-divisor-ℕ : (n d : ℕ) → is-prop (is-proper-divisor-ℕ n d)
is-prop-is-proper-divisor-ℕ n zero-ℕ (pair f g) =
  ex-falso (f (inv (is-zero-div-zero-ℕ n g)))
is-prop-is-proper-divisor-ℕ n (succ-ℕ d) =
  is-prop-prod is-prop-neg (is-prop-div-ℕ (succ-ℕ d) n (is-nonzero-succ-ℕ d))
```

### If a natural number has a proper divisor, then `1` is a proper divisor

```agda
is-proper-divisor-one-is-proper-divisor-ℕ :
  {n x : ℕ} → is-proper-divisor-ℕ n x → is-proper-divisor-ℕ n 1
pr1 (is-proper-divisor-one-is-proper-divisor-ℕ {.1} {x} H) refl =
  pr1 H (is-one-div-one-ℕ x (pr2 H))
pr1 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) = n
pr2 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) =
  right-unit-law-mul-ℕ n
```
