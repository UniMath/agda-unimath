# Lower Dedekind real numbers

```agda
module real-numbers.lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universal-quantification
open import foundation.universe-levels
```

</details>
## Idea

A lower
{{#concept "Dedekind cut" Agda=is-dedekind-cut WD="dedekind cut" WDID=Q851333}}
consists of a [subtype](foundation-core.subtypes.md) `L` of
[the rational numbers](elementary-number-theory.rational-numbers.md) `ℚ`,
satisfying the following two conditions:

1. _Inhabitedness_. `L` is [inhabited](foundation.inhabited-subtypes.md).
2. _Roundedness_. A rational number `q` is in `L`
   [if and only if](foundation.logical-equivalences.md) there
   [exists](foundation.existential-quantification.md) `q < r` such that `r ∈ L`.

The type of all lower Dedekind real numbers is the type of all lower Dedekind
cuts.

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

  is-inhabited-lower-ℝ : exists ℚ cut-lower-ℝ
  is-inhabited-lower-ℝ = pr1 (pr2 x)

  is-rounded-lower-ℝ :
    (q : ℚ) →
    is-in-cut-lower-ℝ q ↔ exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-lower-ℝ r)
  is-rounded-lower-ℝ = pr2 (pr2 x)
```

## Properties

### Lower Dedekind cuts are closed under the standard ordering on the rationals

```agda
module _
  {l : Level} (x : lower-ℝ l) (p q : ℚ)
  where

  le-cut-lower-ℝ : le-ℚ p q → is-in-cut-lower-ℝ x q → is-in-cut-lower-ℝ x p
  le-cut-lower-ℝ p<q q<x =
    backward-implication (is-rounded-lower-ℝ x p) (intro-exists q (p<q , q<x))
```

### Two lower real numbers with the same cut are equal

```agda
module _
  {l : Level} (x y : lower-ℝ l)
  where

  eq-eq-cut-lower-ℝ : cut-lower-ℝ x ＝ cut-lower-ℝ y → x ＝ y
  eq-eq-cut-lower-ℝ = eq-type-subtype is-lower-dedekind-cut-Prop
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
