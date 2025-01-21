# Largest power divisors of natural numbers

```agda
module elementary-number-theory.largest-power-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.finite-maps-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "largest power divisor" Disambiguation="natural numbers" Agda=largest-power-divisor-ℕ}}
of a [natural number](elementary-number-theory.natural-numbers.md) $n$ with base
$m$ is the
[largest number](elementary-number-theory.maximal-structured-natural-numbers.md)
of the form $m^k$ that
[divides](elementary-number-theory.divisibility-natural-numbers.md) $n$.

## Definitions

### Power divisors of natural numbers

```agda
is-power-divisor-ℕ : ℕ → ℕ → ℕ → UU lzero
is-power-divisor-ℕ m n x = is-exponential-ℕ m x × div-ℕ x n
```

### The predicate of being the largest power divisor of a natural number

```agda
is-largest-power-divisor-ℕ : ℕ → ℕ → ℕ → UU lzero
is-largest-power-divisor-ℕ m n x =
  (y : ℕ) → is-power-divisor-ℕ m n y ↔ div-ℕ y x
```

### The largest power divisor of a natural number

```agda
module _
  (m n : ℕ) (H : 1 <-ℕ m) (K : 1 ≤-ℕ n)
  where

  largest-power-divisor-ℕ :
    maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
  largest-power-divisor-ℕ =
    maximal-structured-value-bound-input-property-is-finite-map-ℕ
      ( is-divisor-ℕ n)
      ( λ x → is-decidable-div-ℕ x n)
      ( m ^ℕ_)
      ( is-finite-map-exp-ℕ m H)
      ( n)
      ( 0)
      ( K)
      ( div-one-ℕ n)

  valuation-largest-power-divisor-ℕ :
    ℕ
  valuation-largest-power-divisor-ℕ =
    nat-maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
      ( largest-power-divisor-ℕ)

  upper-bound-exp-valuation-largest-power-divisor-ℕ :
    m ^ℕ valuation-largest-power-divisor-ℕ ≤-ℕ n
  upper-bound-exp-valuation-largest-power-divisor-ℕ =
    pr1
      ( structure-maximal-element-ℕ
        ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
        ( largest-power-divisor-ℕ))

  div-exp-valuation-largest-power-divisor-ℕ :
    div-ℕ (m ^ℕ valuation-largest-power-divisor-ℕ) n
  div-exp-valuation-largest-power-divisor-ℕ =
    pr2
      ( structure-maximal-element-ℕ
        ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
        ( largest-power-divisor-ℕ))

  is-upper-bound-valuation-largest-power-divisor-ℕ :
    (k : ℕ) → div-ℕ (m ^ℕ k) n → k ≤-ℕ valuation-largest-power-divisor-ℕ
  is-upper-bound-valuation-largest-power-divisor-ℕ k L =
    is-upper-bound-maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
      ( largest-power-divisor-ℕ)
      ( k)
      ( leq-div-ℕ (m ^ℕ k) n (is-nonzero-leq-one-ℕ n K) L , L)

  is-largest-power-divisor-valuation-largest-power-divisor-ℕ :
    is-largest-power-divisor-ℕ m n valuation-largest-power-divisor-ℕ
  is-largest-power-divisor-valuation-largest-power-divisor-ℕ =
    {!is-least-upper-bound-is-upper-bound-ℕ!}
```

## See also

- [2-adic decomposition](elementary-number-theory.2-adic-decomposition.md)
