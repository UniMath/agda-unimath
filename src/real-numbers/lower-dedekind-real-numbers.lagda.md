# Lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.dependent-products-truncated-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universal-quantification
open import foundation.universe-levels
```

</details>

## Idea

A [subtype](foundation-core.subtypes.md) `L` of
[the rational numbers](elementary-number-theory.rational-numbers.md) is a
{{#concept "lower Dedekind cut" Agda=is-lower-dedekind-cut}} if it satisfies the
following two conditions:

1. _Inhabitedness_. `L` is [inhabited](foundation.inhabited-subtypes.md).
2. _Lower roundedness_. A rational number `q` is in `L`
   [if and only if](foundation.logical-equivalences.md) there
   [exists](foundation.existential-quantification.md) `q < r` such that `r ∈ L`.

The {{#concept "lower Dedekind real numbers" Agda=lower-ℝ}} is the type of all
lower Dedekind cuts.

## Definition

### Lower Dedekind cuts

```agda
module _
  {l : Level}
  (L : subtype l ℚ)
  where

  is-lower-dedekind-cut-Prop : Prop l
  is-lower-dedekind-cut-Prop =
    (∃ ℚ L) ∧
    (∀' ℚ (λ q → L q ⇔ (∃ ℚ (λ r → le-ℚ-Prop q r ∧ L r))))

  is-lower-dedekind-cut : UU l
  is-lower-dedekind-cut = type-Prop is-lower-dedekind-cut-Prop
```

## The lower Dedekind real numbers

```agda
lower-ℝ : (l : Level) → UU (lsuc l)
lower-ℝ l = Σ (subtype l ℚ) is-lower-dedekind-cut

module _
  {l : Level}
  (x : lower-ℝ l)
  where

  cut-lower-ℝ : subtype l ℚ
  cut-lower-ℝ = pr1 x

  is-in-cut-lower-ℝ : ℚ → UU l
  is-in-cut-lower-ℝ = is-in-subtype cut-lower-ℝ

  is-lower-dedekind-cut-lower-ℝ : is-lower-dedekind-cut cut-lower-ℝ
  is-lower-dedekind-cut-lower-ℝ = pr2 x

  is-inhabited-cut-lower-ℝ : exists ℚ cut-lower-ℝ
  is-inhabited-cut-lower-ℝ = pr1 (pr2 x)

  is-rounded-cut-lower-ℝ :
    (q : ℚ) →
    is-in-cut-lower-ℝ q ↔ exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-lower-ℝ r)
  is-rounded-cut-lower-ℝ = pr2 (pr2 x)
```

## Properties

### The greatest lower Dedekind real

There is a largest lower Dedekind real whose cut is all rational numbers. We
call this element **infinity**.

```agda
infinity-lower-ℝ : lower-ℝ lzero
pr1 infinity-lower-ℝ _ = unit-Prop
pr1 (pr2 infinity-lower-ℝ) = intro-exists zero-ℚ star
pr1 (pr2 (pr2 infinity-lower-ℝ) q) _ =
  intro-exists (q +ℚ one-ℚ) (le-right-add-rational-ℚ⁺ q one-ℚ⁺ , star)
pr2 (pr2 (pr2 infinity-lower-ℝ) q) _ = star
```

### The lower Dedekind reals form a set

```agda
abstract
  is-set-lower-ℝ : (l : Level) → is-set (lower-ℝ l)
  is-set-lower-ℝ l =
    is-set-Σ
      ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
      ( λ q → is-set-is-prop (is-prop-type-Prop (is-lower-dedekind-cut-Prop q)))
```

### Lower Dedekind cuts are closed under strict inequality on the rationals

```agda
module _
  {l : Level} (x : lower-ℝ l) (p q : ℚ)
  where

  is-in-cut-le-ℚ-lower-ℝ :
    le-ℚ p q → is-in-cut-lower-ℝ x q → is-in-cut-lower-ℝ x p
  is-in-cut-le-ℚ-lower-ℝ p<q q<x =
    backward-implication
      ( is-rounded-cut-lower-ℝ x p)
      ( intro-exists q (p<q , q<x))
```

### Lower Dedekind cuts are closed under subtraction by positive rational numbers

```agda
module _
  {l : Level} (x : lower-ℝ l) (p : ℚ) (d : ℚ⁺)
  where

  is-in-cut-diff-rational-ℚ⁺-lower-ℝ :
    is-in-cut-lower-ℝ x p → is-in-cut-lower-ℝ x (p -ℚ rational-ℚ⁺ d)
  is-in-cut-diff-rational-ℚ⁺-lower-ℝ =
    is-in-cut-le-ℚ-lower-ℝ x (p -ℚ rational-ℚ⁺ d) p (le-diff-rational-ℚ⁺ p d)
```

### Lower Dedekind cuts are closed under inequality on the rationals

```agda
module _
  {l : Level} (x : lower-ℝ l) (p q : ℚ)
  where

  is-in-cut-leq-ℚ-lower-ℝ :
    leq-ℚ p q → is-in-cut-lower-ℝ x q → is-in-cut-lower-ℝ x p
  is-in-cut-leq-ℚ-lower-ℝ p≤q q<x with decide-le-leq-ℚ p q
  ... | inl p<q = is-in-cut-le-ℚ-lower-ℝ x p q p<q q<x
  ... | inr q≤p = tr (is-in-cut-lower-ℝ x) (antisymmetric-leq-ℚ q p q≤p p≤q) q<x
```

### Two lower real numbers with the same cut are equal

```agda
module _
  {l : Level} (x y : lower-ℝ l)
  where

  eq-eq-cut-lower-ℝ : cut-lower-ℝ x ＝ cut-lower-ℝ y → x ＝ y
  eq-eq-cut-lower-ℝ = eq-type-subtype is-lower-dedekind-cut-Prop

  eq-sim-cut-lower-ℝ : sim-subtype (cut-lower-ℝ x) (cut-lower-ℝ y) → x ＝ y
  eq-sim-cut-lower-ℝ =
    eq-eq-cut-lower-ℝ ∘ eq-sim-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)
```

## See also

- Upper Dedekind cuts, the dual structure, are defined in
  [`real-numbers.upper-dedekind-real-numbers`](real-numbers.upper-dedekind-real-numbers.md).
- Dedekind cuts, which form the usual real numbers, are defined in
  [`real-numbers.dedekind-real-numbers`](real-numbers.dedekind-real-numbers.md)

## References

This page follows the terminology used in the exercises of Section 11 in
{{#cite UF13}}.

{{#bibliography}}
