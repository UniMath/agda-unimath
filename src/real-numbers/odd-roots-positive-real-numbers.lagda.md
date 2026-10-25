# Odd roots of positive real numbers

```agda
module real-numbers.odd-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.odd-roots-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

For [odd](elementary-number-theory.parity-natural-numbers.md) $n$, the function
$x ↦ \root{n}{x}$ is defined on the
[positive real numbers](real-numbers.positive-real-numbers.md) as the inverse
function to the [power](real-numbers.powers-positive-real-numbers.md) operation
$x ↦ x^n$.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-positive-root-is-odd-exponent-real-ℝ⁺ :
      (x : ℝ⁺ l) →
      is-positive-ℝ (root-is-odd-exponent-ℝ n odd-n (real-ℝ⁺ x))
    is-positive-root-is-odd-exponent-real-ℝ⁺ x⁺@(x , 0<x) =
      tr
        ( λ y → le-ℝ y (root-is-odd-exponent-ℝ n odd-n x))
        ( root-zero-is-odd-exponent-ℝ n odd-n)
        ( preserves-le-root-is-odd-exponent-ℝ n odd-n 0<x)

  root-is-odd-exponent-ℝ⁺ : ℝ⁺ l → ℝ⁺ l
  root-is-odd-exponent-ℝ⁺ x⁺@(x , _) =
    ( root-is-odd-exponent-ℝ n odd-n x ,
      is-positive-root-is-odd-exponent-real-ℝ⁺ x⁺)
```

## Properties

### The root operation is the inverse of the power operation for positive real numbers

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-section-root-is-odd-exponent-ℝ⁺ :
      (x : ℝ⁺ l) → power-ℝ⁺ n (root-is-odd-exponent-ℝ⁺ n odd-n x) ＝ x
    is-section-root-is-odd-exponent-ℝ⁺ (x , _) =
      eq-ℝ⁺ _ _
        ( real-power-ℝ⁺ n _ ∙ is-section-root-is-odd-exponent-ℝ n odd-n x)

    is-retraction-root-is-odd-exponent-ℝ⁺ :
      (x : ℝ⁺ l) → root-is-odd-exponent-ℝ⁺ n odd-n (power-ℝ⁺ n x) ＝ x
    is-retraction-root-is-odd-exponent-ℝ⁺ x⁺@(x , _) =
      eq-ℝ⁺ _ _
        ( ( ap (root-is-odd-exponent-ℝ n odd-n) (real-power-ℝ⁺ n x⁺)) ∙
          ( is-retraction-root-is-odd-exponent-ℝ n odd-n x))

  is-equiv-power-is-odd-exponent-ℝ⁺ : is-equiv (power-ℝ⁺ {l} n)
  is-equiv-power-is-odd-exponent-ℝ⁺ =
    is-equiv-is-invertible
      ( root-is-odd-exponent-ℝ⁺ n odd-n)
      ( is-section-root-is-odd-exponent-ℝ⁺)
      ( is-retraction-root-is-odd-exponent-ℝ⁺)

  aut-power-is-odd-exponent-ℝ⁺ : Aut (ℝ⁺ l)
  aut-power-is-odd-exponent-ℝ⁺ =
    ( power-ℝ⁺ n ,
      is-equiv-power-is-odd-exponent-ℝ⁺)
```
