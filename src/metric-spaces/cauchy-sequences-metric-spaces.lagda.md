# Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in a metric space" WD="cauchy sequence" WDID=Q217847 Agda=cauchy-sequence-Metric-Space}}
`x` in a [metric space](metric-spaces.metric-spaces.md) `X` is a
[sequence](metric-spaces.sequences-metric-spaces.md) of elements of `X` such
that there [exists](foundation.propositional-truncations.md) a
[modulus](metric-spaces.modulated-cauchy-sequences-metric-spaces.md) making it a
modulated Cauchy sequence.

## Definition

### Cauchy sequences

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (x : sequence-type-Metric-Space X)
  where

  is-cauchy-sequence-prop-Metric-Space : Prop l2
  is-cauchy-sequence-prop-Metric-Space =
    trunc-Prop (cauchy-modulus-sequence-Metric-Space X x)

  is-cauchy-sequence-Metric-Space : UU l2
  is-cauchy-sequence-Metric-Space =
    type-Prop is-cauchy-sequence-prop-Metric-Space

cauchy-sequence-Metric-Space :
  {l1 l2 : Level} → Metric-Space l1 l2 → UU (l1 ⊔ l2)
cauchy-sequence-Metric-Space X =
  type-subtype (is-cauchy-sequence-prop-Metric-Space X)

cauchy-sequence-modulated-cauchy-sequence-Metric-Space :
  {l1 l2 : Level} (M : Metric-Space l1 l2) →
  modulated-cauchy-sequence-Metric-Space M →
  cauchy-sequence-Metric-Space M
cauchy-sequence-modulated-cauchy-sequence-Metric-Space
  M (x , μx) = (x , unit-trunc-Prop μx)

module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space X)
  where

  seq-cauchy-sequence-Metric-Space : sequence-type-Metric-Space X
  seq-cauchy-sequence-Metric-Space = pr1 x

  is-cauchy-sequence-seq-cauchy-sequence-Metric-Space :
    is-cauchy-sequence-Metric-Space X seq-cauchy-sequence-Metric-Space
  is-cauchy-sequence-seq-cauchy-sequence-Metric-Space = pr2 x
```

## Properties

### A sequence with a limit is Cauchy

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  {x : sequence-type-Metric-Space X}
  where

  abstract
    is-cauchy-has-limit-sequence-Metric-Space :
      has-limit-sequence-Metric-Space X x → is-cauchy-sequence-Metric-Space X x
    is-cauchy-has-limit-sequence-Metric-Space (lim , is-lim-x) =
      map-trunc-Prop
        ( has-cauchy-modulus-has-limit-modulus-sequence-Metric-Space X x lim)
        ( is-lim-x)
```

### Pairing of Cauchy sequences

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (u : cauchy-sequence-Metric-Space A)
  (v : cauchy-sequence-Metric-Space B)
  where

  seq-pair-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space (product-Metric-Space A B)
  seq-pair-cauchy-sequence-Metric-Space =
    pair-sequence
      ( seq-cauchy-sequence-Metric-Space A u)
      ( seq-cauchy-sequence-Metric-Space B v)

  abstract
    is-cauchy-seq-pair-cauchy-sequence-Metric-Space :
      is-cauchy-sequence-Metric-Space
        ( product-Metric-Space A B)
        ( seq-pair-cauchy-sequence-Metric-Space)
    is-cauchy-seq-pair-cauchy-sequence-Metric-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-cauchy-sequence-prop-Metric-Space
              ( product-Metric-Space A B)
              ( seq-pair-cauchy-sequence-Metric-Space))
      in do
        μ-u ← is-cauchy-sequence-seq-cauchy-sequence-Metric-Space A u
        μ-v ← is-cauchy-sequence-seq-cauchy-sequence-Metric-Space B v
        unit-trunc-Prop
          ( is-cauchy-seq-pair-modulated-cauchy-sequence-Metric-Space
            ( A)
            ( B)
            ( seq-cauchy-sequence-Metric-Space A u , μ-u)
            ( seq-cauchy-sequence-Metric-Space B v , μ-v))

  pair-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space (product-Metric-Space A B)
  pair-cauchy-sequence-Metric-Space =
    ( seq-pair-cauchy-sequence-Metric-Space ,
      is-cauchy-seq-pair-cauchy-sequence-Metric-Space)
```

### To show a sequence `a` is Cauchy, it suffices to have a modulus function `μ` such that for any `ε`, `a (μ ε)` and `a (μ ε + k)` are in an `ε`-neighborhood

```agda
module
  _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (a : sequence-type-Metric-Space X)
  (μ : ℚ⁺ → ℕ)
  where

  abstract
    is-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space :
      ( (ε : ℚ⁺) (k : ℕ) →
        neighborhood-Metric-Space X ε (a (μ ε)) (a (μ ε +ℕ k))) →
      is-cauchy-sequence-Metric-Space X a
    is-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space H =
      unit-trunc-Prop
        ( cauchy-modulus-neighborhood-add-sequence-Metric-Space X a μ H)
```

## See also

- [Cauchy sequences in complete metric spaces](metric-spaces.cauchy-sequences-complete-metric-spaces.md)

## External links

- [Cauchy sequences](https://en.wikipedia.org/wiki/Cauchy_sequence) at Wikipedia
