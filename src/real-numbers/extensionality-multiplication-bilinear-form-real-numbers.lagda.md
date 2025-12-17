# Extensionality of multiplication of real numbers as a bilinear form

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.extensionality-multiplication-bilinear-form-real-numbers where
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
open import real-numbers.zero-real-numbers
```

</details>

## Idea

If the [square](real-numbers.squares-real-numbers.md) of a
[real number](real-numbers.dedekind-real-numbers.md) is
[similar](real-numbers.similarity-real-numbers.md) to 0, the real number is
similar to 0. This property is extensionality of multiplication as a
[bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md) over the
[real vector space of real numbers](linear-algebra.real-vector-spaces.md).

## Proof

```agda
abstract
  is-zero-is-zero-square-ℝ :
    {l : Level} (x : ℝ l) → is-zero-ℝ (square-ℝ x) → is-zero-ℝ x
  is-zero-is-zero-square-ℝ x x²~0 =
    is-zero-is-zero-abs-ℝ
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
    {l : Level} (x : ℝ l) → square-ℝ x ＝ raise-zero-ℝ l →
    x ＝ raise-zero-ℝ l
  eq-zero-eq-zero-square-ℝ {l} x x²=0 =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ l zero-ℝ)
        ( is-zero-is-zero-square-ℝ
          ( x)
          ( transitive-sim-ℝ _ _ _ (sim-raise-ℝ' l zero-ℝ) (sim-eq-ℝ x²=0))))
```
