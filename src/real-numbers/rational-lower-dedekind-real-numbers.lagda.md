# Rational lower Dedekind real numbers

```agda
module real-numbers.rational-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

There is a canonical mapping from the
[rational numbers](elementary-number-theory.rational-numbers.md) to the
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md).

## Definition

```agda
module _
  (q : ℚ)
  where

  cut-lower-real-ℚ : subtype lzero ℚ
  cut-lower-real-ℚ p = le-ℚ-Prop p q

  is-in-cut-lower-real-ℚ : ℚ → UU lzero
  is-in-cut-lower-real-ℚ p = le-ℚ p q

  is-inhabited-cut-lower-real-ℚ : exists ℚ cut-lower-real-ℚ
  is-inhabited-cut-lower-real-ℚ = exists-lesser-ℚ q

  is-rounded-cut-lower-real-ℚ :
    (p : ℚ) →
    le-ℚ p q ↔ exists ℚ (λ r → le-ℚ-Prop p r ∧ le-ℚ-Prop r q)
  pr1 (is-rounded-cut-lower-real-ℚ p) p<q =
    intro-exists
      ( mediant-ℚ p q)
      ( le-left-mediant-ℚ p<q , le-right-mediant-ℚ p<q)
  pr2 (is-rounded-cut-lower-real-ℚ p) =
    elim-exists
      ( le-ℚ-Prop p q)
      ( λ r (p<r , r<q) → transitive-le-ℚ p r q r<q p<r)

  lower-real-ℚ : lower-ℝ lzero
  pr1 lower-real-ℚ = cut-lower-real-ℚ
  pr1 (pr2 lower-real-ℚ) = is-inhabited-cut-lower-real-ℚ
  pr2 (pr2 lower-real-ℚ) = is-rounded-cut-lower-real-ℚ
```
