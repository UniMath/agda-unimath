# Powers of negative real numbers

```agda
module real-numbers.powers-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.squares-negative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

This page describes properties of [powers](real-numbers.powers-real-numbers.md)
of [negative real numbers](real-numbers.negative-real-numbers.md).

## Properties

### Even powers of negative real numbers are positive

```agda
abstract
  is-positive-even-power-ℝ⁻ :
    {l : Level} (n : ℕ) (x : ℝ⁻ l) → is-even-ℕ n →
    is-positive-ℝ (power-ℝ n (real-ℝ⁻ x))
  is-positive-even-power-ℝ⁻ _ x (k , refl) =
    inv-tr
      ( is-positive-ℝ)
      ( power-mul-ℝ' k 2)
      ( is-positive-power-real-ℝ⁺ k (square-ℝ⁻ x))
```

### Odd powers of negative real numbers are negative

```agda
abstract
  is-negative-odd-power-ℝ⁻ :
    {l : Level} (n : ℕ) (x : ℝ⁻ l) → is-odd-ℕ n →
    is-negative-ℝ (power-ℝ n (real-ℝ⁻ x))
  is-negative-odd-power-ℝ⁻ n x⁻@(x , is-neg-x) odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      tr
        ( is-negative-ℝ)
        ( equational-reasoning
          power-ℝ (k *ℕ 2) x *ℝ x
          ＝ power-ℝ (succ-ℕ (k *ℕ 2)) x
            by inv (power-succ-ℝ (k *ℕ 2) _)
          ＝ power-ℝ n x
            by ap (λ m → power-ℝ m x) k2+1=n)
        ( is-negative-mul-positive-negative-ℝ
          ( is-positive-even-power-ℝ⁻ _ x⁻ (k , refl))
          ( is-neg-x))
```
