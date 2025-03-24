# Rational upper Dedekind real numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers.rational-upper-dedekind-real-numbers
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

open import real-numbers.upper-dedekind-real-numbers funext univalence truncations
```

</details>

## Idea

There is a canonical mapping from the
[rational numbers](elementary-number-theory.rational-numbers.md) to the
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md).

## Definition

```agda
module _
  (q : ℚ)
  where

  cut-upper-real-ℚ : subtype lzero ℚ
  cut-upper-real-ℚ = le-ℚ-Prop q

  is-in-cut-upper-real-ℚ : ℚ → UU lzero
  is-in-cut-upper-real-ℚ = le-ℚ q

  is-inhabited-cut-upper-real-ℚ : exists ℚ cut-upper-real-ℚ
  is-inhabited-cut-upper-real-ℚ = exists-greater-ℚ q

  is-rounded-cut-upper-real-ℚ :
    (p : ℚ) →
    le-ℚ q p ↔ exists ℚ (λ r → le-ℚ-Prop r p ∧ le-ℚ-Prop q r)
  pr1 (is-rounded-cut-upper-real-ℚ p) q<p =
    intro-exists
      ( mediant-ℚ q p)
      ( le-right-mediant-ℚ q p q<p , le-left-mediant-ℚ q p q<p)
  pr2 (is-rounded-cut-upper-real-ℚ p) =
    elim-exists
      ( le-ℚ-Prop q p)
      ( λ r (r<p , q<r) → transitive-le-ℚ q r p r<p q<r)

  upper-real-ℚ : upper-ℝ lzero
  pr1 upper-real-ℚ = cut-upper-real-ℚ
  pr1 (pr2 upper-real-ℚ) = is-inhabited-cut-upper-real-ℚ
  pr2 (pr2 upper-real-ℚ) = is-rounded-cut-upper-real-ℚ
```
