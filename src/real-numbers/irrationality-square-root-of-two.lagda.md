# The irrationality of the square root of two

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.irrationality-square-root-of-two where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.irrationality-square-root-of-two
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The [square root](real-numbers.square-roots-nonnegative-real-numbers.md) of two
is not a [rational real number](real-numbers.rational-real-numbers.md).

The irrationality of the square root of two is the
[1st](literature.100-theorems.md#1) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Proof

```agda
abstract
  irrational-sqrt-two-ℝ :
    ¬ Σ ℚ (is-rational-ℝ (real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ 2)))
  irrational-sqrt-two-ℝ (q , √2=q) =
    neq-two-square-ℚ
      ( q)
      ( is-injective-real-ℚ
        ( equational-reasoning
          real-ℚ (square-ℚ q)
          ＝ square-ℝ (real-ℚ q)
            by inv (square-real-ℚ q)
          ＝ square-ℝ (real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ 2))
            by
              ap
                ( square-ℝ)
                ( inv
                  ( eq-sim-ℝ
                    ( sim-rational-ℝ
                      ( real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ 2) , q , √2=q))))
          ＝ real-ℕ 2
            by eq-real-square-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ 2)))
```

## See also

- [Two is not the square of any rational number](elementary-number-theory.irrationality-square-root-of-two.md)
