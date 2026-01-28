# Multiplication of uniformly continuous real maps on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-uniformly-continuous-real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.images-uniformly-continuous-maps-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.uniformly-continuous-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

Given two
[uniformly continuous maps](real-numbers.uniformly-continuous-maps-proper-closed-intervals-real-numbers.md)
`f` and `g` on the
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]`, the map
`x ↦ f x * g x` is uniformly continuous.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : uniformly-continuous-real-map-proper-closed-interval-ℝ l1 l2 [a,b])
  (g : uniformly-continuous-real-map-proper-closed-interval-ℝ l1 l3 [a,b])
  where

  map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l2 ⊔ l3)
  map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ x =
    pr1 f x *ℝ pr1 g x

  abstract
    is-uniformly-continuous-map-mul-real-map-proper-closed-interval-ℝ :
      is-uniformly-continuous-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ)
    is-uniformly-continuous-map-mul-real-map-proper-closed-interval-ℝ =
      is-uniformly-continuous-map-comp-Metric-Space
        ( metric-space-proper-closed-interval-ℝ l1 [a,b])
        ( product-Metric-Space
          ( subspace-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f))
          ( subspace-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g)))
        ( metric-space-ℝ (l2 ⊔ l3))
        ( _)
        ( _)
        ( is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
          ( product-Metric-Space
            ( subspace-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( subspace-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( g)))
          ( metric-space-ℝ (l2 ⊔ l3))
          ( _)
          ( is-lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ
            ( inhabited-totally-bounded-subset-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( inhabited-totally-bounded-subset-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( g))))
        ( is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
          ( _)
          ( _)
          ( comp-uniformly-continuous-map-Metric-Space _ _ _
            ( product-uniformly-continuous-map-Metric-Space _ _ _ _
              ( uniformly-continuous-map-unit-im-Metric-Space _ _ f)
              ( uniformly-continuous-map-unit-im-Metric-Space _ _ g))
            ( uniformly-continuous-map-isometry-Metric-Space
              ( _)
              ( _)
              ( diagonal-product-isometry-Metric-Space
                ( metric-space-proper-closed-interval-ℝ l1 [a,b])))))

  mul-uniformly-continuous-real-map-proper-closed-interval-ℝ :
    uniformly-continuous-real-map-proper-closed-interval-ℝ l1 (l2 ⊔ l3) [a,b]
  mul-uniformly-continuous-real-map-proper-closed-interval-ℝ =
    ( map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ ,
      is-uniformly-continuous-map-mul-real-map-proper-closed-interval-ℝ)
```
