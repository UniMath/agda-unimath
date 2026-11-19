# The isometry from the Cauchy real numbers to the Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.isometry-cauchy-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.similarity-of-elements-pseudometric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.cauchy-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

There is a canonical isometry of the
[Cauchy real numbers](real-numbers.cauchy-real-numbers.md) in the
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
isometry-cauchy-pseudocompletion-real-ℚ :
  isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-metric-space-ℚ)
    ( cauchy-pseudocompletion-Metric-Space (metric-space-ℝ lzero))
isometry-cauchy-pseudocompletion-real-ℚ =
  isometry-cauchy-pseudocompletion-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-ℝ lzero)
    ( isometry-real-ℚ)

real-approximation-cauchy-approximation-ℚ :
  cauchy-approximation-metric-space-ℚ →
  cauchy-approximation-Metric-Space (metric-space-ℝ lzero)
real-approximation-cauchy-approximation-ℚ =
  map-isometry-cauchy-pseudocompletion-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-ℝ lzero)
    ( isometry-real-ℚ)

real-cauchy-approximation-ℚ :
  cauchy-approximation-Metric-Space metric-space-ℚ →
  ℝ lzero
real-cauchy-approximation-ℚ x =
  lim-cauchy-approximation-ℝ (real-approximation-cauchy-approximation-ℚ x)
```

## Properties

### The map from Cauchy approximations in ℚ to Dedekind real numbers preserves and reflects neighborhoods

```agda
module _
  (d : ℚ⁺)
  (x y : cauchy-approximation-Metric-Space metric-space-ℚ)
  where

  abstract
    is-isometry-real-cauchy-approximation-ℚ :
      neighborhood-cauchy-pseudocompletion-metric-space-ℚ d x y ↔
      neighborhood-ℝ lzero
        ( d)
        ( real-cauchy-approximation-ℚ x)
        ( real-cauchy-approximation-ℚ y)
    is-isometry-real-cauchy-approximation-ℚ =
      logical-equivalence-reasoning
        neighborhood-cauchy-pseudocompletion-metric-space-ℚ d x y
        ↔ neighborhood-cauchy-pseudocompletion-Metric-Space
            ( metric-space-ℝ lzero)
            ( d)
            ( real-approximation-cauchy-approximation-ℚ x)
            ( real-approximation-cauchy-approximation-ℚ y)
          by
            is-isometry-map-isometry-Pseudometric-Space
              ( cauchy-pseudocompletion-metric-space-ℚ)
              ( cauchy-pseudocompletion-Metric-Space (metric-space-ℝ lzero))
              ( isometry-cauchy-pseudocompletion-real-ℚ)
              ( d)
              ( x)
              ( y)
        ↔ neighborhood-ℝ lzero
            ( d)
            ( real-cauchy-approximation-ℚ x)
            ( real-cauchy-approximation-ℚ y)
          by
            same-neighborhoods-limits-cauchy-pseudocompletion-Metric-Space
              ( metric-space-ℝ lzero)
              ( d)
              ( real-approximation-cauchy-approximation-ℚ x)
              ( real-approximation-cauchy-approximation-ℚ y)
              ( real-cauchy-approximation-ℚ x)
              ( real-cauchy-approximation-ℚ y)
              ( is-limit-lim-cauchy-approximation-ℝ _)
              ( is-limit-lim-cauchy-approximation-ℝ _)

isometry-real-cauchy-approximation-ℚ :
  isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-metric-space-ℚ)
    ( pseudometric-space-ℝ lzero)
isometry-real-cauchy-approximation-ℚ =
  ( real-cauchy-approximation-ℚ ,
    is-isometry-real-cauchy-approximation-ℚ)
```

### The Dedekind embedding operation is effective on the equivalence relation of similarity in the Cauchy pseudocompletion of ℚ

```agda
abstract
  is-effective-real-cauchy-approximation-ℚ :
    is-effective
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
        ( metric-space-ℚ))
      ( real-cauchy-approximation-ℚ)
  is-effective-real-cauchy-approximation-ℚ x y =
    equiv-iff'
      ( Id-Prop
        ( ℝ-Set lzero)
        ( real-cauchy-approximation-ℚ x)
        ( real-cauchy-approximation-ℚ y))
      ( sim-prop-cauchy-pseudocompletion-metric-space-ℚ x y)
      ( logical-equivalence-reasoning
        (real-cauchy-approximation-ℚ x ＝ real-cauchy-approximation-ℚ y)
        ↔ sim-cauchy-pseudocompletion-Metric-Space
            ( metric-space-ℝ lzero)
            ( real-approximation-cauchy-approximation-ℚ x)
            ( real-approximation-cauchy-approximation-ℚ y)
          by
            inv-iff
              ( eq-limit-iff-sim-cauchy-pseudocompletion-Metric-Space
                ( metric-space-ℝ lzero)
                ( real-approximation-cauchy-approximation-ℚ x)
                ( real-approximation-cauchy-approximation-ℚ y)
                ( is-limit-lim-cauchy-approximation-ℝ _)
                ( is-limit-lim-cauchy-approximation-ℝ _))
        ↔ sim-cauchy-pseudocompletion-metric-space-ℚ x y
          by
            inv-iff
              ( iff-sim-map-isometry-Pseudometric-Space
                ( cauchy-pseudocompletion-metric-space-ℚ)
                ( cauchy-pseudocompletion-Metric-Space (metric-space-ℝ lzero))
                ( isometry-cauchy-pseudocompletion-real-ℚ)
                ( x)
                ( y)))

reflecting-map-real-cauchy-approximation-ℚ :
  reflecting-map-equivalence-relation
    ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
      ( metric-space-ℚ))
    ( ℝ lzero)
reflecting-map-real-cauchy-approximation-ℚ =
  reflecting-map-equivalence-relation-is-effective
    ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
      ( metric-space-ℚ))
    ( real-cauchy-approximation-ℚ)
    ( is-effective-real-cauchy-approximation-ℚ)
```

### The map from Cauchy real numbers to Dedekind real numbers

```agda
real-cauchy-ℝ : cauchy-ℝ → ℝ lzero
real-cauchy-ℝ =
  inv-precomp-set-quotient
    ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
      ( metric-space-ℚ))
    ( ℝ-Set lzero)
    ( reflecting-map-real-cauchy-approximation-ℚ)

abstract
  compute-real-cauchy-real-cauchy-approximation-ℚ :
    (x : cauchy-approximation-metric-space-ℚ) →
    real-cauchy-ℝ (cauchy-real-cauchy-approximation-ℚ x) ＝
    real-cauchy-approximation-ℚ x
  compute-real-cauchy-real-cauchy-approximation-ℚ =
    is-section-inv-precomp-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
        ( metric-space-ℚ))
      ( ℝ-Set lzero)
      ( reflecting-map-real-cauchy-approximation-ℚ)
```

### The map from Cauchy real numbers to Dedekind real numbers preserves and reflects neighborhoods

```agda
module _
  (d : ℚ⁺) (x y : cauchy-ℝ)
  (let
    equiv-relation-sim =
      equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
        ( metric-space-ℚ))
  where abstract

  is-isometry-real-cauchy-ℝ :
    neighborhood-cauchy-ℝ d x y ↔
    neighborhood-ℝ lzero d (real-cauchy-ℝ x) (real-cauchy-ℝ y)
  is-isometry-real-cauchy-ℝ =
    let
      open
        do-syntax-trunc-Prop
          ( iff-Prop
            ( neighborhood-prop-cauchy-ℝ d x y)
            ( neighborhood-prop-ℝ lzero d (real-cauchy-ℝ x) (real-cauchy-ℝ y)))
      equiv-relation-sim =
        equivalence-relation-sim-cauchy-pseudocompletion-Metric-Space
          ( metric-space-ℚ)
    in do
      (x' , in-x'=x) ← is-surjective-quotient-map equiv-relation-sim x
      (y' , in-y'=y) ← is-surjective-quotient-map equiv-relation-sim y
      binary-tr
        ( λ z w →
          neighborhood-cauchy-ℝ d z w ↔
          neighborhood-ℝ lzero d (real-cauchy-ℝ z) (real-cauchy-ℝ w))
        ( in-x'=x)
        ( in-y'=y)
        ( logical-equivalence-reasoning
          neighborhood-cauchy-ℝ d
            ( cauchy-real-cauchy-approximation-ℚ x')
            ( cauchy-real-cauchy-approximation-ℚ y')
          ↔ neighborhood-cauchy-pseudocompletion-metric-space-ℚ
              ( d)
              ( x')
              ( y')
            by inv-iff (is-isometry-cauchy-real-cauchy-approximation-ℚ d x' y')
          ↔ neighborhood-ℝ
              ( lzero)
              ( d)
              ( real-cauchy-approximation-ℚ x')
              ( real-cauchy-approximation-ℚ y')
            by is-isometry-real-cauchy-approximation-ℚ d x' y'
          ↔ neighborhood-ℝ
              ( lzero)
              ( d)
              ( real-cauchy-ℝ (cauchy-real-cauchy-approximation-ℚ x'))
              ( real-cauchy-ℝ (cauchy-real-cauchy-approximation-ℚ y'))
            by
              iff-equiv
                ( equiv-binary-tr
                  ( neighborhood-ℝ lzero d)
                  ( inv (compute-real-cauchy-real-cauchy-approximation-ℚ x'))
                  ( inv (compute-real-cauchy-real-cauchy-approximation-ℚ y'))))

isometry-real-cauchy-ℝ :
  isometry-Metric-Space
    ( metric-space-cauchy-ℝ)
    ( metric-space-ℝ lzero)
isometry-real-cauchy-ℝ = (real-cauchy-ℝ , is-isometry-real-cauchy-ℝ)
```

### The map from Cauchy reals to Dedekind reals is an embedding

```agda
emb-real-cauchy-ℝ : cauchy-ℝ ↪ ℝ lzero
emb-real-cauchy-ℝ =
  emb-map-isometry-Metric-Space
    ( metric-space-cauchy-ℝ)
    ( metric-space-ℝ lzero)
    ( isometry-real-cauchy-ℝ)
```
