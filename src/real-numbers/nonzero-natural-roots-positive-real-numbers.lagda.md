# Nonzero natural roots of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-natural-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.empty-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-natural-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-positive-real-numbers
open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

For any [nonzero](elementary-number-theory.nonzero-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) `n`, there exists
an inverse to the [power function](real-numbers.powers-real-numbers.md) `x ↦ xⁿ`
on the [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
abstract
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    is-positive-ℝ (real-ℝ⁰⁺ x) →
    is-positive-ℝ (real-root-pair-expansion-ℝ⁰⁺ u v x)
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ 0 v (x , _) 0<x =
    is-positive-odd-root-ℝ _ _ x 0<x
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x⁰⁺ 0<x =
    preserves-is-positive-root-pair-expansion-ℝ⁰⁺
      ( u)
      ( v)
      ( sqrt-ℝ⁰⁺ x⁰⁺)
      ( is-positive-sqrt-is-positive-ℝ⁰⁺ x⁰⁺ 0<x)

  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    is-positive-ℝ (real-ℝ⁰⁺ x) →
    is-positive-ℝ (real-nonzero-nat-root-ℝ⁰⁺ n x)
  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ (succ-ℕ n , H) =
    preserves-is-positive-root-pair-expansion-ℝ⁰⁺ _ _
  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ (0 , H) = ex-falso (H refl)

nonzero-nat-root-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ⁺ l
nonzero-nat-root-ℝ⁺ n x⁺@(x , 0<x) =
  ( real-nonzero-nat-root-ℝ⁰⁺ n (nonnegative-ℝ⁺ x⁺) ,
    preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ n _ 0<x)
```

## Properties

### The `1`st root of `x` is `x`

```agda
abstract
  root-one-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → nonzero-nat-root-ℝ⁺ one-ℕ⁺ x ＝ x
  root-one-ℝ⁺ x =
    eq-ℝ⁺ _ _ (ap real-ℝ⁰⁺ (root-one-ℝ⁰⁺ (nonnegative-ℝ⁺ x)))
```

### Integer powers and roots commute

```agda
abstract
  commute-root-int-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (k : ℤ) (x : ℝ⁺ l) →
    nonzero-nat-root-ℝ⁺ n (int-power-ℝ⁺ k x) ＝
    int-power-ℝ⁺ k (nonzero-nat-root-ℝ⁺ n x)
  commute-root-int-power-ℝ⁺ n k x =
    {!   !}
```

## See also

- [Nonzero natural roots of nonnegative real numbers](real-numbers.nonzero-natural-roots-nonnegative-real-numbers.md)
