# Zero nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.zero-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

A [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real number](real-numbers.dedekind-real-numbers.md) is zero if it is
[similar](real-numbers.similarity-real-numbers.md) to
[zero](real-numbers.rational-real-numbers.md).

## Definition

```agda
is-zero-prop-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → Prop l
is-zero-prop-ℝ⁰⁺ (x , _) = is-zero-prop-ℝ x

is-zero-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → UU l
is-zero-ℝ⁰⁺ (x , _) = is-zero-ℝ x
```

## Properties

### `x` is a zero nonnegative real number if and only if `x ≤ 0`

```agda
abstract
  is-zero-leq-zero-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → leq-ℝ⁰⁺ x zero-ℝ⁰⁺ → is-zero-ℝ⁰⁺ x
  is-zero-leq-zero-ℝ⁰⁺ (x , 0≤x) x≤0 = sim-sim-leq-ℝ (x≤0 , 0≤x)

  leq-zero-is-zero-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → is-zero-ℝ⁰⁺ x → leq-ℝ⁰⁺ x zero-ℝ⁰⁺
  leq-zero-is-zero-ℝ⁰⁺ _ x~0 = leq-sim-ℝ x~0
```

### `x` is a zero nonnegative real number if and only if it equals the appropriate raising of zero

```agda
abstract
  eq-raise-zero-is-zero-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → is-zero-ℝ⁰⁺ x → x ＝ raise-zero-ℝ⁰⁺ l
  eq-raise-zero-is-zero-ℝ⁰⁺ {l} (x , _) x~0 =
    eq-ℝ⁰⁺ _ _ (eq-raise-zero-is-zero-ℝ x~0)

  is-zero-raise-zero-ℝ⁰⁺ : (l : Level) → is-zero-ℝ⁰⁺ (raise-zero-ℝ⁰⁺ l)
  is-zero-raise-zero-ℝ⁰⁺ = is-zero-raise-zero-ℝ

  is-zero-eq-raise-zero-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → x ＝ raise-zero-ℝ⁰⁺ l → is-zero-ℝ⁰⁺ x
  is-zero-eq-raise-zero-ℝ⁰⁺ {l} _ refl = is-zero-raise-zero-ℝ l
```
