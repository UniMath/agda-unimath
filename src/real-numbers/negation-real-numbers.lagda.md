# Negation of real numbers

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers.negation-real-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers funext univalence truncations
open import elementary-number-theory.strict-inequality-rational-numbers funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes funext univalence truncations
open import foundation.disjunction funext univalence truncations
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.subtypes funext univalence truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers funext univalence truncations
open import real-numbers.lower-dedekind-real-numbers funext univalence truncations
open import real-numbers.negation-lower-upper-dedekind-real-numbers funext univalence truncations
open import real-numbers.rational-real-numbers funext univalence truncations
open import real-numbers.upper-dedekind-real-numbers funext univalence truncations
```

</details>

## Idea

The {{#concept "negation" Disambiguation="Dedekind real number" Agda=neg-ℝ}} of
a [Dedekind real number](real-numbers.dedekind-real-numbers.md) with cuts
`(L, U)` has lower cut equal to the negation of elements of `U`, and upper cut
equal to the negation of elements in `L`.

```agda
module _
  {l : Level} (x : ℝ l)
  where

  lower-real-neg-ℝ : lower-ℝ l
  lower-real-neg-ℝ = neg-upper-ℝ (upper-real-ℝ x)

  upper-real-neg-ℝ : upper-ℝ l
  upper-real-neg-ℝ = neg-lower-ℝ (lower-real-ℝ x)

  lower-cut-neg-ℝ : subtype l ℚ
  lower-cut-neg-ℝ = cut-lower-ℝ lower-real-neg-ℝ

  upper-cut-neg-ℝ : subtype l ℚ
  upper-cut-neg-ℝ = cut-upper-ℝ upper-real-neg-ℝ

  is-disjoint-cut-neg-ℝ :
    disjoint-subtype lower-cut-neg-ℝ upper-cut-neg-ℝ
  is-disjoint-cut-neg-ℝ q (in-lower-neg , in-upper-neg) =
    is-disjoint-cut-ℝ x (neg-ℚ q) (in-upper-neg , in-lower-neg)

  is-located-lower-upper-cut-neg-ℝ :
    (q r : ℚ) → le-ℚ q r →
    type-disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r)
  is-located-lower-upper-cut-neg-ℝ q r q<r =
    elim-disjunction
      ( disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r))
      ( inr-disjunction)
      ( inl-disjunction)
      ( is-located-lower-upper-cut-ℝ x (neg-ℚ r) (neg-ℚ q) (neg-le-ℚ q r q<r))

  neg-ℝ : ℝ l
  neg-ℝ =
    real-lower-upper-ℝ
      ( lower-real-neg-ℝ)
      ( upper-real-neg-ℝ)
      ( is-disjoint-cut-neg-ℝ)
      ( is-located-lower-upper-cut-neg-ℝ)
```

## Properties

### The negation function on real numbers is an involution

```agda
neg-neg-ℝ : {l : Level} → (x : ℝ l) → neg-ℝ (neg-ℝ x) ＝ x
neg-neg-ℝ x =
  eq-eq-lower-cut-ℝ
    ( neg-ℝ (neg-ℝ x))
    ( x)
    ( eq-has-same-elements-subtype
      ( lower-cut-ℝ (neg-ℝ (neg-ℝ x)))
      ( lower-cut-ℝ x)
      ( λ q →
        tr (is-in-lower-cut-ℝ x) (neg-neg-ℚ q) ,
        tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q))))
```

### Negation preserves rationality

```agda
neg-Rational-ℝ : {l : Level} → Rational-ℝ l → Rational-ℝ l
neg-Rational-ℝ (x , q , q≮x , x≮q) =
  neg-ℝ x ,
  neg-ℚ q ,
  x≮q ∘ tr (is-in-upper-cut-ℝ x) (neg-neg-ℚ q) ,
  q≮x ∘ tr (is-in-lower-cut-ℝ x) (neg-neg-ℚ q)
```
