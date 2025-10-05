# Prime numbers

```agda
module elementary-number-theory.prime-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A prime number is a natural number of which 1 is the only proper divisor.

## Definition

### The main definition of prime numbers

This is a direct interpretation of what it means to be prime.

```agda
is-prime-ℕ : ℕ → UU lzero
is-prime-ℕ n = (x : ℕ) → (is-proper-divisor-ℕ n x ↔ is-one-ℕ x)

Prime-ℕ : UU lzero
Prime-ℕ = Σ ℕ is-prime-ℕ

module _
  (p : Prime-ℕ)
  where

  nat-Prime-ℕ : ℕ
  nat-Prime-ℕ = pr1 p

  is-prime-Prime-ℕ : is-prime-ℕ nat-Prime-ℕ
  is-prime-Prime-ℕ = pr2 p
```

### Second definition of prime numbers

This is an implementation of the idea of being prime, which is usually taken as
the definition.

```agda
is-one-is-proper-divisor-ℕ : ℕ → UU lzero
is-one-is-proper-divisor-ℕ n =
  (x : ℕ) → is-proper-divisor-ℕ n x → is-one-ℕ x

is-prime-easy-ℕ : ℕ → UU lzero
is-prime-easy-ℕ n = (is-not-one-ℕ n) × (is-one-is-proper-divisor-ℕ n)
```

### Third definition of prime numbers

```agda
has-unique-proper-divisor-ℕ : ℕ → UU lzero
has-unique-proper-divisor-ℕ n = is-torsorial (is-proper-divisor-ℕ n)
```

## Properties

### The number `0` is not a prime

```agda
abstract
  is-nonzero-is-prime-ℕ :
    (n : ℕ) → is-prime-ℕ n → is-nonzero-ℕ n
  is-nonzero-is-prime-ℕ n H p =
    is-not-one-two-ℕ
      ( pr1
        ( H 2)
        ( tr (λ k → 2 ≠ k) (inv p) ( is-nonzero-two-ℕ) ,
          tr (div-ℕ 2) (inv p) (0 , refl)))
```

### The number `1` is not a prime

```agda
abstract
  is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
  is-not-one-is-prime-ℕ n H p = pr1 (pr2 (H 1) refl) (inv p)
```

### A prime is strictly greater than `1`

```agda
abstract
  le-one-is-prime-ℕ :
    (n : ℕ) → is-prime-ℕ n → le-ℕ 1 n
  le-one-is-prime-ℕ 0 x = ex-falso (is-nonzero-is-prime-ℕ 0 x refl)
  le-one-is-prime-ℕ 1 x = ex-falso (is-not-one-is-prime-ℕ 1 x refl)
  le-one-is-prime-ℕ (succ-ℕ (succ-ℕ n)) x = star
```

### Being a prime is a proposition

```agda
abstract
  is-prop-is-prime-ℕ :
    (n : ℕ) → is-prop (is-prime-ℕ n)
  is-prop-is-prime-ℕ n =
    is-prop-Π
      ( λ x →
        is-prop-product
          ( is-prop-Π (λ p → is-set-ℕ x 1))
          ( is-prop-Π (λ p → is-prop-is-proper-divisor-ℕ n x)))

is-prime-ℕ-Prop :
  (n : ℕ) → Prop lzero
pr1 (is-prime-ℕ-Prop n) = is-prime-ℕ n
pr2 (is-prime-ℕ-Prop n) = is-prop-is-prime-ℕ n

abstract
  is-prop-has-unique-proper-divisor-ℕ :
    (n : ℕ) → is-prop (has-unique-proper-divisor-ℕ n)
  is-prop-has-unique-proper-divisor-ℕ n = is-property-is-contr
```

### The three definitions of primes are equivalent

```agda
abstract
  is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
  pr1 (is-prime-easy-is-prime-ℕ n H) = is-not-one-is-prime-ℕ n H
  pr2 (is-prime-easy-is-prime-ℕ n H) x = forward-implication (H x)

  is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
  pr1 (is-prime-is-prime-easy-ℕ n H x) = pr2 H x
  pr1 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) q =
    pr1 H (inv q)
  pr2 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) = div-one-ℕ n

  has-unique-proper-divisor-is-prime-ℕ :
    (n : ℕ) → is-prime-ℕ n → has-unique-proper-divisor-ℕ n
  has-unique-proper-divisor-is-prime-ℕ n H =
    fundamental-theorem-id'
      ( λ x p → backward-implication (H x) (inv p))
      ( λ x →
        is-equiv-has-converse-is-prop
          ( is-set-ℕ 1 x)
          ( is-prop-is-proper-divisor-ℕ n x)
          ( λ p → inv (forward-implication (H x) p)))

  is-prime-has-unique-proper-divisor-ℕ :
    (n : ℕ) → has-unique-proper-divisor-ℕ n → is-prime-ℕ n
  pr1 (is-prime-has-unique-proper-divisor-ℕ n H x) K =
    ap pr1
      ( eq-is-contr H
        { pair x K}
        { pair 1 (is-proper-divisor-one-is-proper-divisor-ℕ K)})
  pr2 (is-prime-has-unique-proper-divisor-ℕ n H .1) refl =
    is-proper-divisor-one-is-proper-divisor-ℕ (pr2 (center H))
```

### Being a prime is decidable

```agda
abstract
  is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
  is-decidable-is-prime-easy-ℕ zero-ℕ =
    inr
      ( λ H →
        is-not-one-two-ℕ (pr2 H 2 (is-proper-divisor-zero-succ-ℕ 1)))
  is-decidable-is-prime-easy-ℕ (succ-ℕ n) =
    is-decidable-product
      ( is-decidable-neg (is-decidable-is-one-ℕ (succ-ℕ n)))
      ( is-decidable-bounded-Π-ℕ
        ( is-proper-divisor-ℕ (succ-ℕ n))
        ( is-one-ℕ)
        ( is-decidable-is-proper-divisor-ℕ (succ-ℕ n))
        ( is-decidable-is-one-ℕ)
        ( succ-ℕ n)
        ( λ x H → leq-div-succ-ℕ x n (pr2 H)))

  is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
  is-decidable-is-prime-ℕ n =
    is-decidable-iff
      ( is-prime-is-prime-easy-ℕ n)
      ( is-prime-easy-is-prime-ℕ n)
      ( is-decidable-is-prime-easy-ℕ n)
```

### The number `2` is a prime

```agda
abstract
  is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ 2
  is-one-is-proper-divisor-two-ℕ zero-ℕ (pair f (pair k p)) =
    ex-falso (f (inv (right-zero-law-mul-ℕ k) ∙ p))
  is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = refl
  is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) =
    ex-falso (f refl)
  is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) =
    ex-falso (leq-div-succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) 1 H)

  is-prime-easy-two-ℕ : is-prime-easy-ℕ 2
  pr1 is-prime-easy-two-ℕ = Eq-eq-ℕ
  pr2 is-prime-easy-two-ℕ = is-one-is-proper-divisor-two-ℕ

  is-prime-two-ℕ : is-prime-ℕ 2
  is-prime-two-ℕ =
    is-prime-is-prime-easy-ℕ 2 is-prime-easy-two-ℕ
```

### If a prime number `p` divides a nonzero number `x`, then `x/p < x`

```agda
abstract
  le-quotient-div-is-prime-ℕ :
    (p x : ℕ) → is-nonzero-ℕ x → is-prime-ℕ p →
    (H : div-ℕ p x) → le-ℕ (quotient-div-ℕ p x H) x
  le-quotient-div-is-prime-ℕ p x N P H =
    le-quotient-div-ℕ p x N H (is-not-one-is-prime-ℕ p P)
```

### If a prime number `p` divides a number `x + 1`, then `(x + 1)/p ≤ x`

```agda
abstract
  leq-quotient-div-is-prime-ℕ :
    (p x : ℕ) → is-prime-ℕ p →
    (H : div-ℕ p (succ-ℕ x)) → leq-ℕ (quotient-div-ℕ p (succ-ℕ x) H) x
  leq-quotient-div-is-prime-ℕ p x P H =
    leq-le-succ-ℕ
      ( quotient-div-ℕ p (succ-ℕ x) H)
      ( x)
      ( le-quotient-div-is-prime-ℕ p (succ-ℕ x) (is-nonzero-succ-ℕ x) P H)
```

## See also

- The
  [fundamental theorem of arithmetic](elementary-number-theory.fundamental-theorem-of-arithmetic.md)
  asserts that every positive natural number can be written uniquely as a
  product of primes.
