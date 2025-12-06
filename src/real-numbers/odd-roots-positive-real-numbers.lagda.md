# Odd roots of positive real numbers

```agda
module real-numbers.odd-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

[Odd roots](real-numbers.odd-roots-real-numbers.md) of
[positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are positive.

## Definition

```agda
module _
  {l : Level} (n : ℕ) (odd-n : is-odd-ℕ n)
  where

  abstract
    is-positive-odd-root-ℝ :
      (x : ℝ l) → is-positive-ℝ x → is-positive-ℝ (odd-root-ℝ n odd-n x)
    is-positive-odd-root-ℝ x 0≤x =
      tr
        ( λ z → le-ℝ z (odd-root-ℝ n odd-n x))
        ( odd-root-zero-ℝ n odd-n)
        ( preserves-le-odd-root-ℝ n odd-n 0≤x)

  odd-root-ℝ⁺ : ℝ⁺ l → ℝ⁺ l
  odd-root-ℝ⁺ (x , 0≤x) =
    ( odd-root-ℝ n odd-n x , is-positive-odd-root-ℝ x 0≤x)

  odd-power-odd-root-ℝ⁺ :
    (x : ℝ⁺ l) → power-ℝ n (real-ℝ⁺ (odd-root-ℝ⁺ x)) ＝ real-ℝ⁺ x
  odd-power-odd-root-ℝ⁺ (x , _) = odd-power-odd-root-ℝ n odd-n x
```
