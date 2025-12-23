# Complex Hilbert spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.complex-hilbert-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.difference-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.metric-space-of-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.complex-banach-spaces
open import linear-algebra.complex-inner-product-spaces
open import linear-algebra.complex-inner-product-spaces-are-normed
open import linear-algebra.complex-vector-spaces
open import linear-algebra.normed-complex-vector-spaces
open import linear-algebra.sesquilinear-forms-complex-vector-spaces

open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

A
{{#concept "complex Hilbert space" WDID=Q190056 WD="Hilbert space" Agda=ℂ-Hilbert-Space}}
is a
[complex inner product space](linear-algebra.complex-inner-product-spaces.md)
for which the [metric space](metric-spaces.metric-spaces.md)
[induced](linear-algebra.complex-inner-product-spaces-are-normed.md) by the
inner product is [complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  is-complete-prop-ℂ-Inner-Product-Space : Prop (l1 ⊔ l2)
  is-complete-prop-ℂ-Inner-Product-Space =
    is-complete-prop-Metric-Space
      ( metric-space-ℂ-Inner-Product-Space V)

  is-complete-ℂ-Inner-Product-Space : UU (l1 ⊔ l2)
  is-complete-ℂ-Inner-Product-Space =
    type-Prop is-complete-prop-ℂ-Inner-Product-Space

ℂ-Hilbert-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℂ-Hilbert-Space l1 l2 =
  type-subtype (is-complete-prop-ℂ-Inner-Product-Space {l1} {l2})

module _
  {l1 l2 : Level}
  (V : ℂ-Hilbert-Space l1 l2)
  where

  inner-product-space-ℂ-Hilbert-Space : ℂ-Inner-Product-Space l1 l2
  inner-product-space-ℂ-Hilbert-Space = pr1 V

  vector-space-ℂ-Hilbert-Space : ℂ-Vector-Space l1 l2
  vector-space-ℂ-Hilbert-Space =
    vector-space-ℂ-Inner-Product-Space inner-product-space-ℂ-Hilbert-Space

  normed-vector-space-ℂ-Hilbert-Space : Normed-ℂ-Vector-Space l1 l2
  normed-vector-space-ℂ-Hilbert-Space =
    normed-vector-space-ℂ-Inner-Product-Space
      ( inner-product-space-ℂ-Hilbert-Space)

  metric-space-ℂ-Hilbert-Space : Metric-Space l2 l1
  metric-space-ℂ-Hilbert-Space =
    metric-space-ℂ-Inner-Product-Space inner-product-space-ℂ-Hilbert-Space

  is-complete-metric-space-ℂ-Hilbert-Space :
    is-complete-Metric-Space metric-space-ℂ-Hilbert-Space
  is-complete-metric-space-ℂ-Hilbert-Space = pr2 V

  type-ℂ-Hilbert-Space : UU l2
  type-ℂ-Hilbert-Space = type-ℂ-Vector-Space vector-space-ℂ-Hilbert-Space

  ab-ℂ-Hilbert-Space : Ab l2
  ab-ℂ-Hilbert-Space = ab-ℂ-Vector-Space vector-space-ℂ-Hilbert-Space

  add-ℂ-Hilbert-Space :
    type-ℂ-Hilbert-Space → type-ℂ-Hilbert-Space → type-ℂ-Hilbert-Space
  add-ℂ-Hilbert-Space = add-Ab ab-ℂ-Hilbert-Space

  neg-ℂ-Hilbert-Space : type-ℂ-Hilbert-Space → type-ℂ-Hilbert-Space
  neg-ℂ-Hilbert-Space = neg-Ab ab-ℂ-Hilbert-Space

  zero-ℂ-Hilbert-Space : type-ℂ-Hilbert-Space
  zero-ℂ-Hilbert-Space = zero-Ab ab-ℂ-Hilbert-Space

  mul-ℂ-Hilbert-Space : ℂ l1 → type-ℂ-Hilbert-Space → type-ℂ-Hilbert-Space
  mul-ℂ-Hilbert-Space = mul-ℂ-Vector-Space vector-space-ℂ-Hilbert-Space

  sesquilinear-form-inner-product-ℂ-Hilbert-Space :
    sesquilinear-form-ℂ-Vector-Space vector-space-ℂ-Hilbert-Space
  sesquilinear-form-inner-product-ℂ-Hilbert-Space =
    sesquilinear-form-inner-product-ℂ-Inner-Product-Space
      ( inner-product-space-ℂ-Hilbert-Space)

  inner-product-ℂ-Hilbert-Space :
    type-ℂ-Hilbert-Space → type-ℂ-Hilbert-Space → ℂ l1
  inner-product-ℂ-Hilbert-Space =
    inner-product-ℂ-Inner-Product-Space inner-product-space-ℂ-Hilbert-Space
```

## Properties

### Any complex Hilbert space is a complex Banach space

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Hilbert-Space l1 l2)
  where

  banach-space-ℂ-Hilbert-Space : ℂ-Banach-Space l1 l2
  banach-space-ℂ-Hilbert-Space =
    ( normed-vector-space-ℂ-Hilbert-Space V ,
      is-complete-metric-space-ℂ-Hilbert-Space V)
```

### The complex numbers are a Hilbert space over themselves

```agda
module _
  (l : Level)
  where

  isometric-eq-metric-space-inner-product-space-ℂ :
    isometric-eq-Metric-Space
      ( metric-space-ℂ l)
      ( metric-space-ℂ-Inner-Product-Space (complex-inner-product-space-ℂ l))
  pr1 isometric-eq-metric-space-inner-product-space-ℂ = refl
  pr2 isometric-eq-metric-space-inner-product-space-ℂ d z w =
    iff-equiv
      ( equiv-tr
        ( λ x → leq-ℝ x (real-ℚ⁺ d))
        ( ap
          ( real-sqrt-ℝ⁰⁺)
          ( eq-ℝ⁰⁺ _ _
            ( inv (ap re-ℂ (eq-squared-magnitude-mul-conjugate-ℂ (z -ℂ w)))))))

  abstract
    eq-metric-space-inner-product-space-ℂ :
      metric-space-ℂ l ＝
      metric-space-ℂ-Inner-Product-Space (complex-inner-product-space-ℂ l)
    eq-metric-space-inner-product-space-ℂ =
      eq-isometric-eq-Metric-Space
        ( metric-space-ℂ l)
        ( metric-space-ℂ-Inner-Product-Space (complex-inner-product-space-ℂ l))
        ( isometric-eq-metric-space-inner-product-space-ℂ)

    is-complete-inner-product-space-ℂ :
      is-complete-ℂ-Inner-Product-Space (complex-inner-product-space-ℂ l)
    is-complete-inner-product-space-ℂ =
      tr
        ( is-complete-Metric-Space)
        ( eq-metric-space-inner-product-space-ℂ)
        ( is-complete-metric-space-ℂ l)

  complex-hilbert-space-ℂ : ℂ-Hilbert-Space l (lsuc l)
  complex-hilbert-space-ℂ =
    ( complex-inner-product-space-ℂ l ,
      is-complete-inner-product-space-ℂ)
```
