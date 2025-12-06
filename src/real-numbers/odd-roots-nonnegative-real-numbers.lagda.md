# Odd roots of nonnegative real numbers

```agda
module real-numbers.odd-roots-nonnegative-real-numbers where
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
open import real-numbers.nonnegative-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.powers-real-numbers
```

</details>

## Idea

[Odd roots](real-numbers.odd-roots-real-numbers.md) of
[nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are nonnegative.

## Definition

```agda
module _
  {l : Level} (n : ℕ) (odd-n : is-odd-ℕ n)
  where

  abstract
    is-nonnegative-root-is-odd-ℝ :
      (x : ℝ l) → is-nonnegative-ℝ x → is-nonnegative-ℝ (root-is-odd-ℝ n odd-n x)
    is-nonnegative-root-is-odd-ℝ x 0≤x =
      tr
        ( λ z → leq-ℝ z (root-is-odd-ℝ n odd-n x))
        ( odd-root-zero-ℝ n odd-n)
        ( preserves-leq-root-is-odd-ℝ n odd-n 0≤x)

  root-is-odd-ℝ⁰⁺ : ℝ⁰⁺ l → ℝ⁰⁺ l
  root-is-odd-ℝ⁰⁺ (x , 0≤x) =
    ( root-is-odd-ℝ n odd-n x , is-nonnegative-root-is-odd-ℝ x 0≤x)

  odd-power-root-is-odd-ℝ⁰⁺ :
    (x : ℝ⁰⁺ l) → power-ℝ n (real-ℝ⁰⁺ (root-is-odd-ℝ⁰⁺ x)) ＝ real-ℝ⁰⁺ x
  odd-power-root-is-odd-ℝ⁰⁺ (x , _) = odd-power-root-is-odd-ℝ n odd-n x
```
