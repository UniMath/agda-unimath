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
[real number](real-numbers.dedekind-real-numbers.md) is equal to 0, the real
number is 0. This property is extensionality of multiplication as a
[bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md) over the
[real vector space of real numbers](linear-algebra.real-vector-spaces.md).

## Proof

```agda
abstract
  eq-zero-eq-zero-square-ℝ :
    {l : Level} (x : ℝ l) → square-ℝ x ＝ raise-zero-ℝ l →
    x ＝ raise-zero-ℝ l
  eq-zero-eq-zero-square-ℝ {l} x x²=0 =
    eq-raise-zero-is-zero-ℝ
      ( is-zero-is-zero-square-ℝ
        ( is-zero-eq-raise-zero-ℝ x²=0))
```
