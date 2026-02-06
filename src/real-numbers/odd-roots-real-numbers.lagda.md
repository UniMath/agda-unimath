# Odd roots of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.odd-roots-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
open import real-numbers.unbounded-above-and-below-strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
```

</details>

## Idea

For [odd](elementary-number-theory.parity-natural-numbers.md) $n$, the function
$x ↦ \root{n}{x}$ is defined on the
[real numbers](real-numbers.dedekind-real-numbers.md) as the inverse function to
the [power](real-numbers.powers-real-numbers.md) operation $x ↦ x^n$.

## Definition

```agda
module _
  (l : Level)
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-exponent-ℝ :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l)
  unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-exponent-ℝ =
    ( ( pointwise-ε-δ-continuous-power-ℝ l n ,
        is-strictly-increasing-power-is-odd-exponent-ℝ l n odd-n) ,
      is-unbounded-above-power-is-odd-exponent-ℝ l n odd-n ,
      is-unbounded-below-power-is-odd-exponent-ℝ l n odd-n)

  aut-power-is-odd-exponent-ℝ : Aut (ℝ l)
  aut-power-is-odd-exponent-ℝ =
    aut-unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-exponent-ℝ)

root-is-odd-exponent-ℝ : {l : Level} (n : ℕ) → is-odd-ℕ n → ℝ l → ℝ l
root-is-odd-exponent-ℝ {l} n odd-n =
  map-inv-equiv (aut-power-is-odd-exponent-ℝ l n odd-n)
```

## Properties

### For odd `n`, `n`th roots are the inverse operation to `n`th powers

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x : ℝ l)
  where

  abstract
    is-section-root-is-odd-exponent-ℝ :
      power-ℝ n (root-is-odd-exponent-ℝ n odd-n x) ＝ x
    is-section-root-is-odd-exponent-ℝ =
      is-section-map-inv-equiv (aut-power-is-odd-exponent-ℝ l n odd-n) x

    is-retraction-root-is-odd-exponent-ℝ :
      root-is-odd-exponent-ℝ n odd-n (power-ℝ n x) ＝ x
    is-retraction-root-is-odd-exponent-ℝ =
      is-retraction-map-inv-equiv (aut-power-is-odd-exponent-ℝ l n odd-n) x
```

### For odd `n`, the `n`th root operation preserves strict inequality

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-strictly-increasing-root-is-odd-exponent-ℝ :
      is-strictly-increasing-endomap-ℝ (root-is-odd-exponent-ℝ {l} n odd-n)
    is-strictly-increasing-root-is-odd-exponent-ℝ =
      is-strictly-increasing-map-inv-unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-exponent-ℝ
          ( l)
          ( n)
          ( odd-n))
```

### For odd `n`, the `n`th root operation preserves inequality

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-increasing-root-is-odd-exponent-ℝ :
      is-increasing-endomap-ℝ (root-is-odd-exponent-ℝ {l} n odd-n)
    is-increasing-root-is-odd-exponent-ℝ =
      is-increasing-is-strictly-increasing-endomap-ℝ
        ( root-is-odd-exponent-ℝ n odd-n)
        ( is-strictly-increasing-root-is-odd-exponent-ℝ n odd-n)
```
