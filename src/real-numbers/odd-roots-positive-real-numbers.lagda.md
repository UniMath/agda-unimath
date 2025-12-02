# Nonzero natural roots of real numbers

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
open import real-numbers.inequality-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.powers-real-numbers
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
        ( λ z → leq-ℝ z (odd-root-ℝ n odd-n x))
        ( odd-root-zero-ℝ n odd-n)
        ( preserves-leq-odd-root-ℝ n odd-n 0≤x)

  odd-root-ℝ⁰⁺ : ℝ⁰⁺ l → ℝ⁰⁺ l
  odd-root-ℝ⁰⁺ (x , 0≤x) =
    ( odd-root-ℝ n odd-n x , is-positive-odd-root-ℝ x 0≤x)

  odd-power-odd-root-ℝ⁰⁺ :
    (x : ℝ⁰⁺ l) → power-ℝ n (real-ℝ⁰⁺ (odd-root-ℝ⁰⁺ x)) ＝ real-ℝ⁰⁺ x
  odd-power-odd-root-ℝ⁰⁺ (x , _) = odd-power-odd-root-ℝ n odd-n x
```
