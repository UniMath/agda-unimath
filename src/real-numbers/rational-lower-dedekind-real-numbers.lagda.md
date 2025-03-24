# Rational lower Dedekind real numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers.rational-lower-dedekind-real-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers funext univalence truncations
open import elementary-number-theory.strict-inequality-rational-numbers funext univalence truncations

open import foundation.conjunction funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.existential-quantification funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import real-numbers.lower-dedekind-real-numbers funext univalence truncations
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
      ( le-left-mediant-ℚ p q p<q , le-right-mediant-ℚ p q p<q)
  pr2 (is-rounded-cut-lower-real-ℚ p) =
    elim-exists
      ( le-ℚ-Prop p q)
      ( λ r (p<r , r<q) → transitive-le-ℚ p r q r<q p<r)

  lower-real-ℚ : lower-ℝ lzero
  pr1 lower-real-ℚ = cut-lower-real-ℚ
  pr1 (pr2 lower-real-ℚ) = is-inhabited-cut-lower-real-ℚ
  pr2 (pr2 lower-real-ℚ) = is-rounded-cut-lower-real-ℚ
```
