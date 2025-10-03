# Absolute value on closed intervals in the rational numbers

```agda
module elementary-number-theory.absolute-value-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-nonnegative-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The
[absolute value](elementary-number-theory.absolute-value-rational-numbers.md) of
an element of a
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
[a, b] of [rational numbers](elementary-number-theory.rational-numbers.md) is
bounded by `max(|a|, |b|)`.

## Definition

```agda
max-abs-closed-interval-ℚ : closed-interval-ℚ → ℚ⁰⁺
max-abs-closed-interval-ℚ ((p , q) , p≤q) = max-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q)

rational-max-abs-closed-interval-ℚ : closed-interval-ℚ → ℚ
rational-max-abs-closed-interval-ℚ [p,q] =
  rational-ℚ⁰⁺ (max-abs-closed-interval-ℚ [p,q])
```

## Properties

### If `r ∈ [p,q]`, then `|r| ≤ max(|p|, |q|)`

```agda
abstract
  leq-max-abs-is-in-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r : ℚ) → is-in-closed-interval-ℚ [p,q] r →
    leq-ℚ⁰⁺ (abs-ℚ r) (max-abs-closed-interval-ℚ [p,q])
  leq-max-abs-is-in-closed-interval-ℚ ((p , q) , p≤q) r (p≤r , r≤q) =
    rec-coproduct
      ( λ r≤0 →
        transitive-leq-ℚ
          ( rational-abs-ℚ r)
          ( rational-abs-ℚ p)
          ( max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
          ( leq-left-max-ℚ _ _)
          ( leq-abs-leq-leq-neg-ℚ
            ( r)
            ( rational-abs-ℚ p)
            ( transitive-leq-ℚ r zero-ℚ (rational-abs-ℚ p)
              ( leq-zero-rational-ℚ⁰⁺ (abs-ℚ p))
              ( r≤0))
            ( transitive-leq-ℚ (neg-ℚ r) (neg-ℚ p) (rational-abs-ℚ p)
              ( neg-leq-abs-ℚ p)
              ( neg-leq-ℚ _ _ p≤r))))
      ( λ 0≤r →
        transitive-leq-ℚ
          ( rational-abs-ℚ r)
          ( rational-abs-ℚ q)
          ( max-ℚ (rational-abs-ℚ p) (rational-abs-ℚ q))
          ( leq-right-max-ℚ _ _)
          ( binary-tr
            ( leq-ℚ)
            ( inv (rational-abs-zero-leq-ℚ r 0≤r))
            ( inv
              ( rational-abs-zero-leq-ℚ
                ( q)
                ( transitive-leq-ℚ zero-ℚ r q r≤q 0≤r)))
            ( r≤q)))
      ( linear-leq-ℚ r zero-ℚ)
```
