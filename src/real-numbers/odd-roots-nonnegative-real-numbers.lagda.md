# Odd roots of nonnegative real numbers

```agda
module real-numbers.odd-roots-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.powers-nonnegative-real-numbers
open import real-numbers.powers-real-numbers
```

</details>

## Idea

For [odd](elementary-number-theory.parity-natural-numbers.md) $n$, the function
$x ↦ \root{n}{x}$ is defined on the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) as the
inverse function to the [power](real-numbers.powers-nonnegative-real-numbers.md)
operation $x ↦ x^n$.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l)
  where

  abstract
    is-nonnegative-root-is-odd-exponent-real-ℝ⁰⁺ :
      is-nonnegative-ℝ (root-is-odd-exponent-ℝ n odd-n x)
    is-nonnegative-root-is-odd-exponent-real-ℝ⁰⁺ =
      tr
        ( λ y → leq-ℝ y (root-is-odd-exponent-ℝ n odd-n x))
        ( root-zero-is-odd-exponent-ℝ n odd-n)
        ( preserves-leq-root-is-odd-exponent-ℝ n odd-n 0≤x)

  root-is-odd-exponent-ℝ⁰⁺ : ℝ⁰⁺ l
  root-is-odd-exponent-ℝ⁰⁺ =
    ( root-is-odd-exponent-ℝ n odd-n x ,
      is-nonnegative-root-is-odd-exponent-real-ℝ⁰⁺)
```

## Properties

### The root operation is the inverse operation to the power operation on odd exponents

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l)
  where

  abstract
    is-section-root-is-odd-exponent-ℝ⁰⁺ :
      power-ℝ⁰⁺ n (root-is-odd-exponent-ℝ⁰⁺ n odd-n x⁰⁺) ＝ x⁰⁺
    is-section-root-is-odd-exponent-ℝ⁰⁺ =
      eq-ℝ⁰⁺ _ _
        ( real-power-ℝ⁰⁺ n _ ∙ is-section-root-is-odd-exponent-ℝ n odd-n x)

    is-retraction-root-is-odd-exponent-ℝ⁰⁺ :
      root-is-odd-exponent-ℝ⁰⁺ n odd-n (power-ℝ⁰⁺ n x⁰⁺) ＝ x⁰⁺
    is-retraction-root-is-odd-exponent-ℝ⁰⁺ =
      eq-ℝ⁰⁺ _ _
        ( ( ap (root-is-odd-exponent-ℝ n odd-n) (real-power-ℝ⁰⁺ n x⁰⁺)) ∙
          ( is-retraction-root-is-odd-exponent-ℝ n odd-n x))

module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  is-equiv-power-is-odd-exponent-ℝ⁰⁺ : is-equiv (power-ℝ⁰⁺ {l} n)
  is-equiv-power-is-odd-exponent-ℝ⁰⁺ =
    is-equiv-is-invertible
      ( root-is-odd-exponent-ℝ⁰⁺ n odd-n)
      ( is-section-root-is-odd-exponent-ℝ⁰⁺ n odd-n)
      ( is-retraction-root-is-odd-exponent-ℝ⁰⁺ n odd-n)

  aut-power-is-odd-exponent-ℝ⁰⁺ : Aut (ℝ⁰⁺ l)
  aut-power-is-odd-exponent-ℝ⁰⁺ =
    ( power-ℝ⁰⁺ n ,
      is-equiv-power-is-odd-exponent-ℝ⁰⁺)
```
