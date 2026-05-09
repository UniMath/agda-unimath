# The sequence of reciprocal of factorials of natural numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.reciprocal-factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.factorials
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The sequence of {{#concept "reciprocal of factorials" Agda=inv-factorial-ℕ}} is
the sequence `ℕ → ℚ` defined by `n ↦ 1/n!`.

For any `k l n : ℕ` such that `n ＝ k + l`,

```text
  1/n! * binomial-coefficient-ℕ n k ＝ 1/k! * 1/l!
```

where `binomial-coefficient-ℕ` is the
[binomial coefficient](elementary-number-theory.binomial-coefficients.md)

## Definitions

### The sequence of inverses of factorials

```agda
positive-inv-factorial-ℕ : ℕ → ℚ⁺
positive-inv-factorial-ℕ =
  positive-reciprocal-rational-ℕ⁺ ∘ nonzero-factorial-ℕ

inv-factorial-ℕ : ℕ → ℚ
inv-factorial-ℕ = rational-ℚ⁺ ∘ positive-inv-factorial-ℕ
```

## Properties

### Computation rule with the binomial coefficients

For any `n k l : ℕ` such that `n = k + l`,

```text
   1/n! * (choose n k) ＝ 1/k! * 1/l!
```

where `choose n k` is the
[binomial coefficient](elementary-number-theory.binomial-coefficients.md).

```agda
abstract
  rational-binomal-coeffictient-factorial-formula-ℕ :
    ( k l : ℕ) →
    ( mul-ℚ
      ( rational-ℕ (binomial-coefficient-ℕ (k +ℕ l) k))
      ( rational-ℕ
        ( factorial-ℕ k *ℕ factorial-ℕ l))) ＝
    ( rational-ℕ (factorial-ℕ (k +ℕ l)))
  rational-binomal-coeffictient-factorial-formula-ℕ k l =
    mul-rational-ℕ
      ( binomial-coefficient-ℕ (k +ℕ l) k)
      ( factorial-ℕ k *ℕ factorial-ℕ l) ∙
    ap
      ( rational-ℕ)
      ( binomial-coefficient-factorial-formula-ℕ k l)

  binomial-coefficient-inv-factorial-formula-ℕ :
    ( k l : ℕ) →
    ( mul-ℚ
      ( inv-factorial-ℕ (k +ℕ l))
      ( rational-ℕ (binomial-coefficient-ℕ (k +ℕ l) k))) ＝
    ( mul-ℚ
      ( inv-factorial-ℕ k)
      ( inv-factorial-ℕ l))
  binomial-coefficient-inv-factorial-formula-ℕ k l =
    lemma-swap-inv-mul
      ( positive-rational-ℕ⁺
        ( mul-nonzero-ℕ
          ( nonzero-factorial-ℕ k)
          ( nonzero-factorial-ℕ l)))
      ( positive-rational-ℕ⁺ (nonzero-factorial-ℕ (k +ℕ l)))
      ( rational-ℕ (binomial-coefficient-ℕ (k +ℕ l) k))
      ( rational-binomal-coeffictient-factorial-formula-ℕ k l) ∙
    distributive-reciprocal-mul-ℕ⁺ _ _
    where

    lemma-swap-inv-mul :
      (u v : ℚ⁺) (x : ℚ) →
      x *ℚ rational-ℚ⁺ u ＝ rational-ℚ⁺ v →
      rational-inv-ℚ⁺ v *ℚ x ＝ rational-inv-ℚ⁺ u
    lemma-swap-inv-mul u@(u' , u>0) v@(v' , v>0) x H =
      equational-reasoning
        rational-inv-ℚ⁺ v *ℚ x
        ＝ rational-inv-ℚ⁺ v *ℚ x *ℚ one-ℚ
          by inv (right-unit-law-mul-ℚ (rational-inv-ℚ⁺ v *ℚ x))
        ＝ rational-inv-ℚ⁺ v *ℚ x *ℚ (rational-inv-ℚ⁺ u *ℚ rational-ℚ⁺ u)
          by
            ap
              ( mul-ℚ (rational-inv-ℚ⁺ v *ℚ x) ∘ rational-ℚ⁺)
              ( inv (left-inverse-law-mul-ℚ⁺ u))
        ＝ (rational-inv-ℚ⁺ u *ℚ rational-ℚ⁺ u) *ℚ (rational-inv-ℚ⁺ v *ℚ x)
          by commutative-mul-ℚ _ _
        ＝ (rational-inv-ℚ⁺ u *ℚ rational-inv-ℚ⁺ v) *ℚ (rational-ℚ⁺ u *ℚ x)
          by interchange-law-mul-mul-ℚ _ _ _ _
        ＝ (rational-inv-ℚ⁺ u *ℚ rational-inv-ℚ⁺ v) *ℚ rational-ℚ⁺ v
          by
            ap
              ( mul-ℚ (rational-inv-ℚ⁺ u *ℚ rational-inv-ℚ⁺ v))
              ( commutative-mul-ℚ _ _ ∙ H)
        ＝ rational-inv-ℚ⁺ u
          by
            associative-mul-ℚ _ _ _ ∙
            ap
              ( mul-ℚ (rational-inv-ℚ⁺ u) ∘ rational-ℚ⁺)
              ( left-inverse-law-mul-ℚ⁺ v) ∙
            right-unit-law-mul-ℚ _

  binomial-coefficient-split-inv-factorial-formula-ℕ :
    (n k l : ℕ) →
    (n ＝ k +ℕ l) →
    mul-ℚ
      ( inv-factorial-ℕ n)
      ( rational-ℕ (binomial-coefficient-ℕ n k)) ＝
    mul-ℚ
      ( inv-factorial-ℕ k)
      ( inv-factorial-ℕ l)
  binomial-coefficient-split-inv-factorial-formula-ℕ n k l n=k+l =
    inv-tr
      ( λ u →
        inv-factorial-ℕ u *ℚ (rational-ℕ (binomial-coefficient-ℕ u k)) ＝
        inv-factorial-ℕ k *ℚ inv-factorial-ℕ l)
      ( n=k+l)
      ( binomial-coefficient-inv-factorial-formula-ℕ k l)
```
