# Extensionality of squares of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.extensionality-squares-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

If the [square](real-numbers.squares-real-numbers.md) of a
[real number](real-numbers.dedekind-real-numbers.md) is
[similar](real-numbers.similarity-real-numbers.md) to 0, the real number is
similar to 0.

## Proof

```agda
abstract
  sim-zero-sim-zero-square-ℝ :
    {l : Level} (x : ℝ l) → sim-ℝ (square-ℝ x) zero-ℝ → sim-ℝ x zero-ℝ
  sim-zero-sim-zero-square-ℝ x x²~0 =
    sim-zero-sim-zero-abs-ℝ
      ( x)
      ( inv-tr
        ( λ y → sim-ℝ y zero-ℝ)
        ( eq-abs-sqrt-square-ℝ x)
        ( transitive-sim-ℝ _ _ _
          ( sim-eq-ℝ real-sqrt-zero-ℝ⁰⁺)
          ( preserves-sim-sqrt-ℝ⁰⁺
            ( nonnegative-square-ℝ x)
            ( zero-ℝ⁰⁺)
            ( x²~0))))

  eq-zero-eq-zero-square-ℝ :
    {l : Level} (x : ℝ l) → square-ℝ x ＝ raise-ℝ l zero-ℝ →
    x ＝ raise-ℝ l zero-ℝ
  eq-zero-eq-zero-square-ℝ {l} x x²=0 =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ l zero-ℝ)
        ( sim-zero-sim-zero-square-ℝ
          ( x)
          ( transitive-sim-ℝ _ _ _ (sim-raise-ℝ' l zero-ℝ) (sim-eq-ℝ x²=0))))
```
