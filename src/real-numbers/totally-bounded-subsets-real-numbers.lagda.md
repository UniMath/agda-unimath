# Totally bounded subsets of the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.totally-bounded-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces

open import real-numbers.isometry-negation-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "totally bounded" disambiguation="subset of the real numbers" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-subset-ℝ}}
if it is [totally bounded](metric-spaces.totally-bounded-metric-spaces.md) as a
[subspace](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (S : subset-ℝ l1 l2)
  where

  modulus-of-total-boundedness-subset-ℝ : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  modulus-of-total-boundedness-subset-ℝ =
    modulus-of-total-boundedness-Metric-Space l3 (metric-space-subset-ℝ S)

  is-totally-bounded-prop-subset-ℝ : Prop (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-totally-bounded-prop-subset-ℝ =
    is-totally-bounded-prop-Metric-Space l3 (metric-space-subset-ℝ S)

  is-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-totally-bounded-subset-ℝ = type-Prop is-totally-bounded-prop-subset-ℝ

totally-bounded-subset-ℝ : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
totally-bounded-subset-ℝ l1 l2 l3 =
  type-subtype (is-totally-bounded-prop-subset-ℝ {l1} {l2} l3)

module _
  {l1 l2 l3 : Level} (S : totally-bounded-subset-ℝ l1 l2 l3)
  where

  subset-totally-bounded-subset-ℝ : subset-ℝ l1 l2
  subset-totally-bounded-subset-ℝ = pr1 S

  type-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2)
  type-totally-bounded-subset-ℝ = type-subtype subset-totally-bounded-subset-ℝ

  metric-space-totally-bounded-subset-ℝ : Metric-Space (l1 ⊔ lsuc l2) l2
  metric-space-totally-bounded-subset-ℝ =
    metric-space-subset-ℝ subset-totally-bounded-subset-ℝ

  is-totally-bounded-totally-bounded-subset-ℝ :
    is-totally-bounded-subset-ℝ l3 subset-totally-bounded-subset-ℝ
  is-totally-bounded-totally-bounded-subset-ℝ = pr2 S

  is-inhabited-totally-bounded-subset-ℝ : UU (l1 ⊔ lsuc l2)
  is-inhabited-totally-bounded-subset-ℝ =
    is-inhabited-subset-ℝ subset-totally-bounded-subset-ℝ
```

## Properties

### The elementwise negation of a totally bounded subset of ℝ is totally bounded

```agda
module _
  {l1 l2 l3 : Level} (S : totally-bounded-subset-ℝ l1 l2 l3)
  where

  abstract
    is-totally-bounded-neg-totally-bounded-subset-ℝ :
      is-totally-bounded-subset-ℝ
        ( l1 ⊔ lsuc l2 ⊔ l3)
        ( neg-subset-ℝ (subset-totally-bounded-subset-ℝ S))
    is-totally-bounded-neg-totally-bounded-subset-ℝ =
      preserves-is-totally-bounded-isometric-equiv-Metric-Space _ _
        ( is-totally-bounded-im-isometry-is-totally-bounded-Metric-Space
          ( metric-space-totally-bounded-subset-ℝ S)
          ( metric-space-ℝ l2)
          ( is-totally-bounded-totally-bounded-subset-ℝ S)
          ( comp-isometry-Metric-Space
            ( metric-space-totally-bounded-subset-ℝ S)
            ( metric-space-ℝ l2)
            ( metric-space-ℝ l2)
            ( isometry-neg-ℝ)
            ( isometry-inclusion-subspace-Metric-Space
              ( metric-space-ℝ l2)
              ( subset-totally-bounded-subset-ℝ S))))
        ( isometric-equiv-neg-subset-im-neg-subset-ℝ
          ( subset-totally-bounded-subset-ℝ S))

  neg-totally-bounded-subset-ℝ :
    totally-bounded-subset-ℝ l1 l2 (l1 ⊔ lsuc l2 ⊔ l3)
  neg-totally-bounded-subset-ℝ =
    ( neg-subset-ℝ (subset-totally-bounded-subset-ℝ S) ,
      is-totally-bounded-neg-totally-bounded-subset-ℝ)
```
