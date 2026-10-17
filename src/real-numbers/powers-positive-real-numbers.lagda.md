# Powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.multiples-of-elements-large-abelian-groups
open import group-theory.powers-of-elements-large-monoids

open import real-numbers.large-multiplicative-group-of-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a positive real number to a natural number power" Agda=power-ℝ⁺}}
on the [positive real numbers](real-numbers.positive-real-numbers.md)
`n x ↦ xⁿ`, is defined by [iteratively](foundation.iterating-functions.md)
[multiplying](real-numbers.multiplication-positive-real-numbers.md) `x` with
itself `n` times.

## Definition

```agda
power-ℝ⁺ : {l : Level} → ℕ → ℝ⁺ l → ℝ⁺ l
power-ℝ⁺ = multiple-Large-Ab large-ab-mul-ℝ⁺
```

## Properties

### Powers of positive real numbers agree with powers of real numbers

```agda
abstract
  real-power-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) →
    real-ℝ⁺ (power-ℝ⁺ n x) ＝ power-ℝ n (real-ℝ⁺ x)
  real-power-ℝ⁺ = inclusion-power-Large-Submonoid large-submonoid-mul-real-ℝ⁺

  is-positive-power-real-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) → is-positive-ℝ (power-ℝ n (real-ℝ⁺ x))
  is-positive-power-real-ℝ⁺ n x =
    tr
      ( is-positive-ℝ)
      ( real-power-ℝ⁺ n x)
      ( is-positive-real-ℝ⁺ (power-ℝ⁺ n x))
```

### `1ⁿ = 1`

```agda
abstract
  power-raise-one-ℝ⁺ :
    {l : Level} (n : ℕ) → power-ℝ⁺ n (raise-one-ℝ⁺ l) ＝ raise-one-ℝ⁺ l
  power-raise-one-ℝ⁺ {l} =
    raise-power-unit-Large-Monoid large-monoid-mul-ℝ⁺ l
```
