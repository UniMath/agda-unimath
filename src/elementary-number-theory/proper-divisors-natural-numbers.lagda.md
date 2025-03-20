# Proper divisors of natural numbers

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.proper-divisors-natural-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers funext
open import elementary-number-theory.equality-natural-numbers funext
open import elementary-number-theory.inequality-natural-numbers funext
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers funext

open import foundation.cartesian-product-types funext
open import foundation.decidable-types funext
open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.identity-types funext
open import foundation.negated-equality funext
open import foundation.negation funext
open import foundation.propositions funext
open import foundation.type-arithmetic-empty-type funext
open import foundation.universe-levels
```

</details>

## Idea

A proper divisor of a natural number `n` is a natural number `d ≠ n` that
divides `n`.

```agda
is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = (d ≠ n) × (div-ℕ d n)

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-product
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
  is-prop-product is-prop-neg (is-prop-div-ℕ (succ-ℕ d) n (is-nonzero-succ-ℕ d))
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

### If `x` is nonzero and `d | x` is a proper divisor, then `1 < x/d`

```agda
le-one-quotient-div-is-proper-divisor-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) →
  d ≠ x → le-ℕ 1 (quotient-div-ℕ d x H)
le-one-quotient-div-is-proper-divisor-ℕ d x f H g =
  map-left-unit-law-coproduct-is-empty
    ( is-one-ℕ (quotient-div-ℕ d x H))
    ( le-ℕ 1 (quotient-div-ℕ d x H))
    ( map-neg (eq-is-one-quotient-div-ℕ d x H) g)
    ( eq-or-le-leq-ℕ' 1
      ( quotient-div-ℕ d x H)
      ( leq-one-quotient-div-ℕ d x H (leq-one-is-nonzero-ℕ x f)))
```
