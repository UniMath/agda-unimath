# Real sequences approximating zero

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.real-sequences-approximating-zero where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.rational-sequences-approximating-zero

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.limits-of-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) is an
{{#concept "approximation of zero" Disambiguation="sequence of real numbers" Agda=is-zero-limit-sequence-ℝ}}
if it [converges](metric-spaces.limits-of-sequences-metric-spaces.md) to 0 in
the
[standard metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-zero-limit-prop-sequence-ℝ : {l : Level} → sequence (ℝ l) → Prop l
is-zero-limit-prop-sequence-ℝ {l} σ =
  is-limit-prop-sequence-ℝ σ (raise-zero-ℝ l)

is-zero-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU l
is-zero-limit-sequence-ℝ σ = type-Prop (is-zero-limit-prop-sequence-ℝ σ)
```

## Properties

### The canonical embedding of the rational numbers in the real numbers preserves approximations of zero

```agda
abstract
  is-zero-limit-real-is-zero-limit-sequence-ℚ :
    (u : sequence ℚ) →
    is-zero-limit-sequence-ℚ u →
    is-zero-limit-sequence-ℝ (real-ℚ ∘ u)
  is-zero-limit-real-is-zero-limit-sequence-ℚ u H =
    tr
      ( is-limit-sequence-ℝ (real-ℚ ∘ u))
      ( eq-raise-ℝ zero-ℝ)
      ( preserves-limits-sequence-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ lzero)
        ( isometry-real-ℚ)
        ( u)
        ( zero-ℚ)
        ( H))
```

### If the absolute value of a sequence of reals is bounded by a rational approximation of zero, the sequence of reals is an approximation of zero

```agda
abstract
  is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ :
    {l : Level} (a : sequence (ℝ l)) (b : zero-limit-sequence-ℚ) →
    ((n : ℕ) → leq-ℝ (abs-ℝ (a n)) (real-ℚ (seq-zero-limit-sequence-ℚ b n))) →
    is-zero-limit-sequence-ℝ a
  is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ
    {l} a (b , lim-b=0) H =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      map-tot-exists
        ( λ μ is-mod-μ ε n με≤n →
          neighborhood-dist-ℝ
            ( ε)
            ( a n)
            ( raise-zero-ℝ l)
            ( chain-of-inequalities
              dist-ℝ (a n) (raise-zero-ℝ l)
              ≤ dist-ℝ (a n) zero-ℝ
                by
                  leq-sim-ℝ
                    ( preserves-dist-right-sim-ℝ
                      ( symmetric-sim-ℝ (sim-raise-ℝ l zero-ℝ)))
              ≤ abs-ℝ (a n)
                by leq-eq-ℝ (right-zero-law-dist-ℝ (a n))
              ≤ real-ℚ (b n)
                by H n
              ≤ real-ℚ (rational-abs-ℚ (b n))
                by preserves-leq-real-ℚ (leq-abs-ℚ (b n))
              ≤ real-ℚ (rational-dist-ℚ (b n) zero-ℚ)
                by
                  leq-eq-ℝ
                    ( ap
                      ( real-ℚ ∘ rational-ℚ⁰⁺)
                      ( inv (right-zero-law-dist-ℚ (b n))))
              ≤ real-ℚ⁺ ε
                by
                  preserves-leq-real-ℚ
                    ( leq-dist-neighborhood-ℚ ε _ _ (is-mod-μ ε n με≤n))))
        ( lim-b=0)
```

### Left multiplication by a real number preserves approximations of zero

```agda
abstract
  preserves-is-zero-limit-left-mul-sequence-ℝ :
    {l1 l2 : Level} (c : ℝ l1) (u : sequence (ℝ l2)) →
    is-zero-limit-sequence-ℝ u →
    is-zero-limit-sequence-ℝ (mul-ℝ c ∘ u)
  preserves-is-zero-limit-left-mul-sequence-ℝ {l1} {l2} c u u→0 =
    tr
      ( is-limit-sequence-ℝ (mul-ℝ c ∘ u))
      ( eq-sim-ℝ
        ( similarity-reasoning-ℝ
          c *ℝ raise-zero-ℝ l2
          ~ℝ c *ℝ zero-ℝ
            by preserves-sim-left-mul-ℝ c _ _ (sim-raise-ℝ' l2 zero-ℝ)
          ~ℝ zero-ℝ
            by right-zero-law-mul-ℝ c
          ~ℝ raise-zero-ℝ (l1 ⊔ l2)
            by sim-raise-ℝ (l1 ⊔ l2) zero-ℝ))
      ( preserves-limits-sequence-uniformly-continuous-endomap-ℝ
        ( uniformly-continuous-map-right-mul-ℝ l2 c)
        ( u)
        ( _)
        ( u→0))
```

### Homotopies preserve approximations of zero

```agda
module _
  {l : Level}
  {u v : sequence (ℝ l)}
  where

  abstract
    preserves-is-zero-limit-htpy-sequence-ℝ :
      u ~ v → is-zero-limit-sequence-ℝ u → is-zero-limit-sequence-ℝ v
    preserves-is-zero-limit-htpy-sequence-ℝ u~v =
      tr is-zero-limit-sequence-ℝ (eq-htpy u~v)
```
