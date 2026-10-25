# Powers of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.powers-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.powers-of-elements-large-commutative-monoids
open import group-theory.powers-of-elements-large-monoids

open import order-theory.large-posets

open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-multiplicative-monoid-of-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a nonnegative real number to a natural number power" Agda=power-ℝ⁰⁺}}
on the [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md)
`n x ↦ xⁿ`, is defined by [iteratively](foundation.iterating-functions.md)
[multiplying](real-numbers.multiplication-nonnegative-real-numbers.md) `x` with
itself `n` times.

Note that this operation defines`0⁰` to be the empty product, `1`.

## Definition

```agda
power-ℝ⁰⁺ : {l : Level} → ℕ → ℝ⁰⁺ l → ℝ⁰⁺ l
power-ℝ⁰⁺ = power-Large-Monoid large-monoid-mul-ℝ⁰⁺
```

## Properties

### `xᵐⁿ = (xᵐ)ⁿ`

```agda
abstract
  power-mul-ℝ⁰⁺ :
    {l : Level} (m n : ℕ) {x : ℝ⁰⁺ l} →
    power-ℝ⁰⁺ (m *ℕ n) x ＝ power-ℝ⁰⁺ n (power-ℝ⁰⁺ m x)
  power-mul-ℝ⁰⁺ = power-mul-Large-Monoid large-monoid-mul-ℝ⁰⁺
```

### Powers on nonnegative real numbers agree with powers on real numbers

```agda
abstract
  real-power-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁰⁺ l) →
    real-ℝ⁰⁺ (power-ℝ⁰⁺ n x) ＝ power-ℝ n (real-ℝ⁰⁺ x)
  real-power-ℝ⁰⁺ =
    inclusion-power-Large-Submonoid large-submonoid-mul-real-ℝ⁰⁺

  is-nonnegative-power-real-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁰⁺ l) →
    is-nonnegative-ℝ (power-ℝ n (real-ℝ⁰⁺ x))
  is-nonnegative-power-real-ℝ⁰⁺ n x =
    tr
      ( is-nonnegative-ℝ)
      ( real-power-ℝ⁰⁺ n x)
      ( is-nonnegative-real-ℝ⁰⁺ (power-ℝ⁰⁺ n x))
```

### If `x` and `y` are nonnegative such that `x ≤ y`, then `xⁿ ≤ yⁿ`

```agda
abstract
  preserves-leq-power-ℝ⁰⁺ :
    {l1 l2 : Level} (n : ℕ) (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ (power-ℝ⁰⁺ n x) (power-ℝ⁰⁺ n y)
  preserves-leq-power-ℝ⁰⁺ {l1} {l2} 0 _ _ _ =
    leq-sim-ℝ (sim-raise-raise-ℝ l1 l2 one-ℝ)
  preserves-leq-power-ℝ⁰⁺ 1 _ _ x≤y = x≤y
  preserves-leq-power-ℝ⁰⁺ (succ-ℕ n@(succ-ℕ _)) x y x≤y =
    preserves-leq-mul-ℝ⁰⁺
      ( power-ℝ⁰⁺ n x)
      ( power-ℝ⁰⁺ n y)
      ( x)
      ( y)
      ( preserves-leq-power-ℝ⁰⁺ n x y x≤y)
      ( x≤y)

  preserves-leq-power-real-ℝ⁰⁺ :
    {l1 l2 : Level} (n : ℕ) (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → leq-ℝ⁰⁺ x y →
    leq-ℝ (power-ℝ n (real-ℝ⁰⁺ x)) (power-ℝ n (real-ℝ⁰⁺ y))
  preserves-leq-power-real-ℝ⁰⁺ n x y x≤y =
    binary-tr
      ( leq-ℝ)
      ( real-power-ℝ⁰⁺ n x)
      ( real-power-ℝ⁰⁺ n y)
      ( preserves-leq-power-ℝ⁰⁺ n x y x≤y)
```

### `(xy)ⁿ = xⁿyⁿ`

```agda
abstract
  distributive-power-mul-ℝ⁰⁺ :
    {l1 l2 : Level} (n : ℕ) {x : ℝ⁰⁺ l1} {y : ℝ⁰⁺ l2} →
    power-ℝ⁰⁺ n (x *ℝ⁰⁺ y) ＝ power-ℝ⁰⁺ n x *ℝ⁰⁺ power-ℝ⁰⁺ n y
  distributive-power-mul-ℝ⁰⁺ =
    distributive-power-mul-Large-Commutative-Monoid
      ( large-commutative-monoid-mul-ℝ⁰⁺)
```

### `1ⁿ = 1`

```agda
abstract
  power-raise-one-ℝ⁰⁺ :
    {l : Level} (n : ℕ) → power-ℝ⁰⁺ n (raise-one-ℝ⁰⁺ l) ＝ raise-one-ℝ⁰⁺ l
  power-raise-one-ℝ⁰⁺ {l} =
    raise-power-unit-Large-Monoid large-monoid-mul-ℝ⁰⁺ l
```
