# Unsolvability of squaring to two in the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.unsolvability-of-squaring-to-two-in-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.squares-integers
open import elementary-number-theory.squares-natural-numbers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
```

</details>

## Idea

There is no [rational number](elementary-number-theory.rational-numbers.md)
whose [square](elementary-number-theory.squares-rational-numbers.md) is two.

The irrationality of the square root of two is the
[1st](literature.100-theorems.md#1) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

This file proves that two is not the square of any rational number.

## Proof

```agda
abstract opaque
  unfolding rational-fraction-ℤ mul-ℚ

  is-not-square-two-ℚ : ¬ (is-square-ℚ (rational-ℕ 2))
  is-not-square-two-ℚ ((p/q@(p , q⁺@(q , is-pos-q)) , coprime-p-q) , 2=p²/q²) =
    let
      qℕ = succ-ℕ (nat-positive-ℤ q⁺)
      qℕ=q : int-ℕ qℕ ＝ q
      qℕ=q =
        inv (int-positive-int-ℕ _) ∙ ap int-ℤ⁺ (is-section-nat-positive-ℤ q⁺)
      |p|²=qℕ²2 : square-ℕ (abs-ℤ p) ＝ square-ℕ qℕ *ℕ 2
      |p|²=qℕ²2 =
        is-injective-int-ℕ
          ( equational-reasoning
              int-ℕ (square-ℕ (abs-ℤ p))
              ＝ square-ℤ p
                by square-abs-ℤ p
              ＝ square-ℤ p *ℤ one-ℤ
                by inv (right-unit-law-mul-ℤ _)
              ＝ int-ℕ 2 *ℤ square-ℤ q
                by
                  sim-fraction-ℤ-eq-ℚ
                    ( mul-fraction-ℤ p/q p/q)
                    ( in-fraction-ℤ (int-ℕ 2))
                    ( ( inv 2=p²/q²) ∙
                      ( inv (is-retraction-rational-fraction-ℚ (rational-ℕ 2))))
              ＝ int-ℕ 2 *ℤ square-ℤ (int-ℕ qℕ)
                by ap-mul-ℤ refl (ap square-ℤ (inv qℕ=q))
              ＝ int-ℕ 2 *ℤ int-ℕ (square-ℕ qℕ)
                by ap-mul-ℤ refl (square-int-ℕ qℕ)
              ＝ int-ℕ (2 *ℕ square-ℕ qℕ)
                by mul-int-ℕ _ _
              ＝ int-ℕ (square-ℕ qℕ *ℕ 2)
                by ap int-ℕ (commutative-mul-ℕ 2 (square-ℕ qℕ)))
      (k , k2=|p|) =
        is-even-is-even-square-ℕ (abs-ℤ p) (square-ℕ qℕ , inv |p|²=qℕ²2)
      k²2=qℕ² : square-ℕ k *ℕ 2 ＝ square-ℕ qℕ
      k²2=qℕ² =
        is-injective-right-mul-succ-ℕ
          ( 1)
          ( equational-reasoning
            square-ℕ k *ℕ 2 *ℕ 2
            ＝ square-ℕ k *ℕ square-ℕ 2
              by associative-mul-ℕ (square-ℕ k) 2 2
            ＝ square-ℕ (k *ℕ 2)
              by inv (distributive-square-mul-ℕ k 2)
            ＝ square-ℕ (abs-ℤ p)
              by ap square-ℕ k2=|p|
            ＝ square-ℕ qℕ *ℕ 2
              by |p|²=qℕ²2)
      (l , l2=qℕ) = is-even-is-even-square-ℕ qℕ (square-ℕ k , k²2=qℕ²)
    in
      rec-coproduct
        ( neq-le-ℤ' (int-ℕ 2) one-ℤ _)
        ( neq-le-ℤ' (int-ℕ 2) neg-one-ℤ _)
        ( is-one-or-neg-one-is-unit-ℤ
          ( int-ℕ 2)
          ( is-unit-div-relatively-prime-ℤ
            ( p)
            ( q)
            ( int-ℕ 2)
            ( coprime-p-q)
            ( rec-coproduct
                ( λ p=|p| →
                  ( int-ℕ k , mul-int-ℕ k 2 ∙ ap int-ℕ k2=|p| ∙ inv p=|p|))
                ( λ p=-|p| →
                  ( neg-ℤ (int-ℕ k) ,
                    ( left-negative-law-mul-ℤ _ _) ∙
                    ( ap neg-ℤ (mul-int-ℕ k 2)) ∙
                    ( ap (neg-ℤ ∘ int-ℕ) k2=|p|) ∙
                    ( inv p=-|p|)))
                ( is-pos-or-neg-abs-ℤ p) ,
              ( int-ℕ l , mul-int-ℕ l 2 ∙ ap int-ℕ l2=qℕ ∙ qℕ=q))))
```

## See also

- [The square root of 2 as a real number is irrational](real-numbers.irrationality-square-root-of-two.md)
