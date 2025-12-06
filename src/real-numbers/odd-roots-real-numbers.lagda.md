# Odd roots of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.odd-roots-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.invertibility-strictly-increasing-unbounded-continuous-functions-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

For any [odd](elementary-number-theory.parity-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) `n`, the `n`th
{{#concept "root" Disambiguation="odd roots of real numbers" Agda=root-is-odd-ℝ}}
operation is a map from `ℝ` to `ℝ` that is the inverse operation to the `n`th
[power](real-numbers.powers-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  opaque
    root-is-odd-ℝ : ℝ l → ℝ l
    root-is-odd-ℝ = map-inv-SIPCUB-function-ℝ (SIPCUB-power-is-odd-ℝ l n odd-n)

  abstract opaque
    unfolding root-is-odd-ℝ

    power-root-is-odd-ℝ :
      (x : ℝ l) → power-ℝ n (root-is-odd-ℝ x) ＝ x
    power-root-is-odd-ℝ =
      is-section-map-inv-SIPCUB-function-ℝ (SIPCUB-power-is-odd-ℝ l n odd-n)

    root-power-is-odd-ℝ :
      (x : ℝ l) → root-is-odd-ℝ (power-ℝ n x) ＝ x
    root-power-is-odd-ℝ =
      is-retraction-map-inv-SIPCUB-function-ℝ (SIPCUB-power-is-odd-ℝ l n odd-n)
```

## Properties

### Odd roots preserve strict inequality

```agda
module _
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    preserves-le-root-is-odd-ℝ :
      {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → le-ℝ x y →
      le-ℝ (root-is-odd-ℝ n odd-n x) (root-is-odd-ℝ n odd-n y)
    preserves-le-root-is-odd-ℝ {x = x} {y = y} x<y =
      reflects-le-power-is-odd-ℝ
        ( n)
        ( odd-n)
        ( _)
        ( _)
        ( binary-tr
          ( le-ℝ)
          ( inv (power-root-is-odd-ℝ n odd-n x))
          ( inv (power-root-is-odd-ℝ n odd-n y))
          ( x<y))
```

### Odd roots preserve inequality

```agda
module _
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    preserves-leq-root-is-odd-ℝ :
      {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → leq-ℝ x y →
      leq-ℝ (root-is-odd-ℝ n odd-n x) (root-is-odd-ℝ n odd-n y)
    preserves-leq-root-is-odd-ℝ {x = x} {y = y} x≤y =
      reflects-leq-power-is-odd-ℝ
        ( n)
        ( odd-n)
        ( _)
        ( _)
        ( binary-tr
          ( leq-ℝ)
          ( inv (power-root-is-odd-ℝ n odd-n x))
          ( inv (power-root-is-odd-ℝ n odd-n y))
          ( x≤y))
```

### Odd roots are injective

```agda
module _
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract opaque
    unfolding root-is-odd-ℝ

    is-injective-root-is-odd-ℝ :
      {l : Level} → is-injective (root-is-odd-ℝ {l} n odd-n)
    is-injective-root-is-odd-ℝ {l} =
      is-injective-map-inv-SIPCUB-function-ℝ (SIPCUB-power-is-odd-ℝ l n odd-n)
```

### Any odd root of 0 is 0

```agda
abstract
  odd-root-zero-ℝ :
    (n : ℕ) (odd-n : is-odd-ℕ n) → root-is-odd-ℝ n odd-n zero-ℝ ＝ zero-ℝ
  odd-root-zero-ℝ n odd-n =
    is-injective-odd-power-ℝ
      ( n)
      ( odd-n)
      ( equational-reasoning
        power-ℝ n (root-is-odd-ℝ n odd-n zero-ℝ)
        ＝ zero-ℝ
          by power-root-is-odd-ℝ n odd-n zero-ℝ
        ＝ power-ℝ n zero-ℝ
          by inv (nonzero-power-zero-ℝ (n , is-nonzero-is-odd-ℕ odd-n)))
```
