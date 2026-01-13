# Odd roots of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.odd-roots-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
open import real-numbers.unbounded-above-and-below-strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
```

</details>

## Idea

For [odd](elementary-number-theory.parity-natural-numbers.md) `n`, the function
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

  unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-ℝ :
    unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l)
  unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-ℝ =
    ( ( pointwise-ε-δ-continuous-power-ℝ l n ,
        is-strictly-increasing-power-is-odd-ℝ l n odd-n) ,
      is-unbounded-above-power-is-odd-ℝ l n odd-n ,
      is-unbounded-below-power-is-odd-ℝ l n odd-n)

  aut-power-is-odd-ℝ : Aut (ℝ l)
  aut-power-is-odd-ℝ =
    aut-unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-ℝ)

root-is-odd-ℝ : {l : Level} (n : ℕ) → is-odd-ℕ n → ℝ l → ℝ l
root-is-odd-ℝ {l} n odd-n = map-inv-equiv (aut-power-is-odd-ℝ l n odd-n)
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
    is-section-root-is-odd-ℝ : power-ℝ n (root-is-odd-ℝ n odd-n x) ＝ x
    is-section-root-is-odd-ℝ =
      is-section-map-inv-equiv (aut-power-is-odd-ℝ l n odd-n) x

    is-retraction-root-is-odd-ℝ : root-is-odd-ℝ n odd-n (power-ℝ n x) ＝ x
    is-retraction-root-is-odd-ℝ =
      is-retraction-map-inv-equiv (aut-power-is-odd-ℝ l n odd-n) x
```

### `n`th roots preserve similarity

```agda
abstract
  preserves-sim-root-is-odd-ℝ :
    {l1 l2 : Level} (n : ℕ) (odd-n : is-odd-ℕ n) →
    {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y →
    sim-ℝ (root-is-odd-ℝ n odd-n x) (root-is-odd-ℝ n odd-n y)
  preserves-sim-root-is-odd-ℝ {l1} {l2} n odd-n {x} {y} x~y =
    sim-eq-raise-ℝ
      ( is-injective-power-is-odd-ℝ
        ( l1 ⊔ l2)
        ( n)
        ( odd-n)
        ( equational-reasoning
          power-ℝ n (raise-ℝ l2 (root-is-odd-ℝ n odd-n x))
          ＝ raise-ℝ l2 (power-ℝ n (root-is-odd-ℝ n odd-n x))
            by power-raise-ℝ l2 n _
          ＝ raise-ℝ l2 x
            by ap (raise-ℝ l2) (is-section-root-is-odd-ℝ n odd-n x)
          ＝ raise-ℝ l1 y
            by eq-raise-sim-ℝ x~y
          ＝ raise-ℝ l1 (power-ℝ n (root-is-odd-ℝ n odd-n y))
            by ap (raise-ℝ l1) (inv (is-section-root-is-odd-ℝ n odd-n y))
          ＝ power-ℝ n (raise-ℝ l1 (root-is-odd-ℝ n odd-n y))
            by inv (power-raise-ℝ l1 n _)))

  root-is-odd-raise-ℝ :
    {l0 : Level} (l : Level) (n : ℕ) (odd-n : is-odd-ℕ n) (x : ℝ l0) →
    root-is-odd-ℝ n odd-n (raise-ℝ l x) ＝ raise-ℝ l (root-is-odd-ℝ n odd-n x)
  root-is-odd-raise-ℝ {l0} l n odd-n x =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ l _)
        ( preserves-sim-root-is-odd-ℝ n odd-n (sim-raise-ℝ' l x)))
```

### For odd `n`, the `n`th root operation preserves strict inequality

```agda
module _
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-strictly-increasing-root-is-odd-ℝ :
      {l : Level} → is-strictly-increasing-endomap-ℝ (root-is-odd-ℝ {l} n odd-n)
    is-strictly-increasing-root-is-odd-ℝ {l} =
      is-strictly-increasing-map-inv-unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
        ( unbounded-above-and-below-strictly-increasing-pointwise-ε-δ-continuous-endomap-power-is-odd-ℝ
          ( l)
          ( n)
          ( odd-n))

    preserves-le-root-is-odd-ℝ :
      {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
      le-ℝ x y → le-ℝ (root-is-odd-ℝ n odd-n x) (root-is-odd-ℝ n odd-n y)
    preserves-le-root-is-odd-ℝ {l1} {l2} {x} {y} x<y =
      preserves-le-sim-ℝ
        ( preserves-sim-root-is-odd-ℝ n odd-n (sim-raise-ℝ' l2 x))
        ( preserves-sim-root-is-odd-ℝ n odd-n (sim-raise-ℝ' l1 y))
        ( is-strictly-increasing-root-is-odd-ℝ
          ( raise-ℝ l2 x)
          ( raise-ℝ l1 y)
          ( preserves-le-sim-ℝ (sim-raise-ℝ l2 x) (sim-raise-ℝ l1 y) x<y))
```

### For odd `n`, the `n`th root operation preserves inequality

```agda
module _
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  where

  abstract
    is-increasing-root-is-odd-ℝ :
      {l : Level} → is-increasing-endomap-ℝ (root-is-odd-ℝ {l} n odd-n)
    is-increasing-root-is-odd-ℝ =
      is-increasing-is-strictly-increasing-endomap-ℝ
        ( root-is-odd-ℝ n odd-n)
        ( is-strictly-increasing-root-is-odd-ℝ n odd-n)

    preserves-leq-root-is-odd-ℝ :
      {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
      leq-ℝ x y → leq-ℝ (root-is-odd-ℝ n odd-n x) (root-is-odd-ℝ n odd-n y)
    preserves-leq-root-is-odd-ℝ {l1} {l2} {x} {y} x≤y =
      preserves-leq-sim-ℝ
        ( preserves-sim-root-is-odd-ℝ n odd-n (sim-raise-ℝ' l2 x))
        ( preserves-sim-root-is-odd-ℝ n odd-n (sim-raise-ℝ' l1 y))
        ( is-increasing-root-is-odd-ℝ
          ( raise-ℝ l2 x)
          ( raise-ℝ l1 y)
          ( preserves-leq-sim-ℝ (sim-raise-ℝ l2 x) (sim-raise-ℝ l1 y) x≤y))
```

### For odd `n`, the `n`th root of 0 is 0

```agda
abstract
  root-is-odd-zero-ℝ :
    (n : ℕ) (odd-n : is-odd-ℕ n) → root-is-odd-ℝ n odd-n zero-ℝ ＝ zero-ℝ
  root-is-odd-zero-ℝ n odd-n =
    is-injective-power-is-odd-ℝ
      ( lzero)
      ( n)
      ( odd-n)
      ( equational-reasoning
        power-ℝ n (root-is-odd-ℝ n odd-n zero-ℝ)
        ＝ zero-ℝ
          by is-section-root-is-odd-ℝ n odd-n zero-ℝ
        ＝ power-ℝ n zero-ℝ
          by inv (power-nonzero-zero-ℝ (n , is-nonzero-is-odd-ℕ odd-n)))
```

### For odd `n`, the `n`th root of 1 is 1

```agda
abstract
  root-is-odd-one-ℝ :
    (n : ℕ) (odd-n : is-odd-ℕ n) → root-is-odd-ℝ n odd-n one-ℝ ＝ one-ℝ
  root-is-odd-one-ℝ n odd-n =
    is-injective-power-is-odd-ℝ
      ( lzero)
      ( n)
      ( odd-n)
      ( equational-reasoning
        power-ℝ n (root-is-odd-ℝ n odd-n one-ℝ)
        ＝ one-ℝ
          by is-section-root-is-odd-ℝ n odd-n one-ℝ
        ＝ power-ℝ n one-ℝ
          by inv (power-one-ℝ n))
```

### For odd `n`, the `n`th root of a nonnegative real number is nonnegative

```agda
module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l)
  where

  abstract
    is-nonnegative-root-is-odd-real-ℝ⁰⁺ :
      is-nonnegative-ℝ (root-is-odd-ℝ n odd-n x)
    is-nonnegative-root-is-odd-real-ℝ⁰⁺ =
      tr
        ( λ y → leq-ℝ y (root-is-odd-ℝ n odd-n x))
        ( root-is-odd-zero-ℝ n odd-n)
        ( preserves-leq-root-is-odd-ℝ n odd-n 0≤x)

  root-is-odd-ℝ⁰⁺ : ℝ⁰⁺ l
  root-is-odd-ℝ⁰⁺ =
    ( root-is-odd-ℝ n odd-n x , is-nonnegative-root-is-odd-real-ℝ⁰⁺)

module _
  {l : Level}
  (n : ℕ)
  (odd-n : is-odd-ℕ n)
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l)
  where

  abstract
    is-section-root-is-odd-ℝ⁰⁺ :
      power-ℝ⁰⁺ n (root-is-odd-ℝ⁰⁺ n odd-n x⁰⁺) ＝ x⁰⁺
    is-section-root-is-odd-ℝ⁰⁺ =
      eq-ℝ⁰⁺ _ _ (is-section-root-is-odd-ℝ n odd-n x)

    is-retraction-root-is-odd-ℝ⁰⁺ :
      root-is-odd-ℝ⁰⁺ n odd-n (power-ℝ⁰⁺ n x⁰⁺) ＝ x⁰⁺
    is-retraction-root-is-odd-ℝ⁰⁺ =
      eq-ℝ⁰⁺ _ _ (is-retraction-root-is-odd-ℝ n odd-n x)
```

## See also

- [Nonzero roots of nonnegative real numbers](real-numbers.nonzero-roots-nonnegative-real-numbers.md)
- [Square roots of nonnegative real numbers](real-numbers.square-roots-nonnegative-real-numbers.md)
