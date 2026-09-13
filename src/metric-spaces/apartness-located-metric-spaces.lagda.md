# Apartness in located metric spaces

```agda
module metric-spaces.apartness-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.located-metric-spaces
```

</details>

## Idea

A [located metric space](metric-spaces.located-metric-spaces.md) `M` induces an
[apartness relation](foundation.apartness-relations.md) `#` such that `x # y` if
there [exists](foundation.existential-quantification.md) an `ε : ℚ⁺` such that
`x` and `y` are [not](foundation.negation.md) in an `ε`-neighborhood of each
other.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Located-Metric-Space l1 l2)
  where

  apart-prop-Located-Metric-Space :
    Relation-Prop l2 (type-Located-Metric-Space M)
  apart-prop-Located-Metric-Space x y =
    ∃ ℚ⁺ (λ ε → ¬' neighborhood-prop-Located-Metric-Space M ε x y)

  apart-Located-Metric-Space : Relation l2 (type-Located-Metric-Space M)
  apart-Located-Metric-Space =
    type-Relation-Prop apart-prop-Located-Metric-Space
```

## Properties

### The apartness relation of a located metric space is antireflexive

```agda
module _
  {l1 l2 : Level} (M : Located-Metric-Space l1 l2)
  where

  abstract
    is-antireflexive-apart-Located-Metric-Space :
      is-antireflexive (apart-prop-Located-Metric-Space M)
    is-antireflexive-apart-Located-Metric-Space x =
      elim-exists
        ( empty-Prop)
        ( λ ε ¬Nεxx → ¬Nεxx (refl-neighborhood-Located-Metric-Space M ε x))
```

### The apartness relation of a located metric space is symmetric

```agda
module _
  {l1 l2 : Level} (M : Located-Metric-Space l1 l2)
  where

  abstract
    is-symmetric-apart-Located-Metric-Space :
      is-symmetric (apart-Located-Metric-Space M)
    is-symmetric-apart-Located-Metric-Space x y =
      map-tot-exists
        ( λ ε ¬Nεxy Nεyx →
          ¬Nεxy (symmetric-neighborhood-Located-Metric-Space M ε y x Nεyx))
```

### The apartness relation of a located metric space is cotransitive

```agda
module _
  {l1 l2 : Level} (M : Located-Metric-Space l1 l2)
  where

  abstract
    is-cotransitive-apart-Located-Metric-Space :
      is-cotransitive (apart-prop-Located-Metric-Space M)
    is-cotransitive-apart-Located-Metric-Space x y z x#z =
      let
        motive =
          ( apart-prop-Located-Metric-Space M x y) ∨
          ( apart-prop-Located-Metric-Space M y z)
        open do-syntax-trunc-Prop motive
      in do
        (dxz , ¬Ndxz) ← x#z
        let (δ , ε , δ+ε=dxz) = split-ℚ⁺ dxz
        elim-disjunction
          ( motive)
          ( λ ¬Nδ'xy →
            inl-disjunction (intro-exists (mediant-zero-ℚ⁺ δ) ¬Nδ'xy))
          ( λ Nδxy →
            elim-disjunction
              ( motive)
              ( λ ¬Nε'yz →
                inr-disjunction (intro-exists (mediant-zero-ℚ⁺ ε) ¬Nε'yz))
              ( λ Nεyz →
                ex-falso
                  ( ¬Ndxz
                    ( tr
                      ( λ d → neighborhood-Located-Metric-Space M d x z)
                      ( δ+ε=dxz)
                      ( triangular-neighborhood-Located-Metric-Space M
                        ( x)
                        ( y)
                        ( z)
                        ( δ)
                        ( ε)
                        ( Nεyz)
                        ( Nδxy)))))
              ( is-located-Located-Metric-Space M
                ( y)
                ( z)
                ( mediant-zero-ℚ⁺ ε)
                ( ε)
                ( le-mediant-zero-ℚ⁺ ε)))
          ( is-located-Located-Metric-Space M
            ( x)
            ( y)
            ( mediant-zero-ℚ⁺ δ)
            ( δ)
            ( le-mediant-zero-ℚ⁺ δ))
```

### The apartness relation on located metric spaces is an apartness relation

```agda
module _
  {l1 l2 : Level} (M : Located-Metric-Space l1 l2)
  where

  is-apartness-relation-apart-Located-Metric-Space :
    is-apartness-relation (apart-prop-Located-Metric-Space M)
  is-apartness-relation-apart-Located-Metric-Space =
    ( is-antireflexive-apart-Located-Metric-Space M ,
      is-symmetric-apart-Located-Metric-Space M ,
      is-cotransitive-apart-Located-Metric-Space M)

  apartness-relation-Located-Metric-Space :
    Apartness-Relation l2 (type-Located-Metric-Space M)
  apartness-relation-Located-Metric-Space =
    ( apart-prop-Located-Metric-Space M ,
      is-apartness-relation-apart-Located-Metric-Space)
```
