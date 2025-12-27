# Multiplication of uniformly continuous functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-uniformly-continuous-functions-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.images-uniformly-continuous-functions-metric-spaces
open import metric-spaces.lipschitz-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers
```

</details>

## Idea

Given two
[uniformly continuous maps](real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers.md)
`f` and `g` on the
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]`, the map
`x ↦ f x * g x` is uniformly continuous.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : ucont-map-proper-closed-interval-ℝ l1 l2 [a,b])
  (g : ucont-map-proper-closed-interval-ℝ l1 l3 [a,b])
  where

  map-mul-ucont-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l2 ⊔ l3)
  map-mul-ucont-map-proper-closed-interval-ℝ x =
    pr1 f x *ℝ pr1 g x

  abstract
    is-ucont-map-mul-ucont-map-proper-closed-interval-ℝ :
      is-ucont-map-proper-closed-interval-ℝ
        ( [a,b])
        ( map-mul-ucont-map-proper-closed-interval-ℝ)
    is-ucont-map-mul-ucont-map-proper-closed-interval-ℝ =
      is-uniformly-continuous-comp-function-Metric-Space
        ( metric-space-proper-closed-interval-ℝ l1 [a,b])
        ( product-Metric-Space
          ( subspace-im-ucont-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f))
          ( subspace-im-ucont-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g)))
        ( metric-space-ℝ (l2 ⊔ l3))
        ( _)
        ( _)
        ( is-uniformly-continuous-is-lipschitz-function-Metric-Space
          ( product-Metric-Space
            ( subspace-im-ucont-map-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( subspace-im-ucont-map-proper-closed-interval-ℝ
              ( [a,b])
              ( g)))
          ( metric-space-ℝ (l2 ⊔ l3))
          ( _)
          ( is-lipschitz-mul-inhabited-totally-bounded-subset-ℝ
            ( inhabited-totally-bounded-subset-im-ucont-map-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( inhabited-totally-bounded-subset-im-ucont-map-proper-closed-interval-ℝ
              ( [a,b])
              ( g))))
        ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
          ( _)
          ( _)
          ( comp-uniformly-continuous-function-Metric-Space _ _ _
            ( product-uniformly-continuous-function-Metric-Space _ _ _ _
              ( uniformly-continuous-map-unit-im-Metric-Space _ _ f)
              ( uniformly-continuous-map-unit-im-Metric-Space _ _ g))
            ( uniformly-continuous-isometry-Metric-Space
              ( _)
              ( _)
              ( diagonal-product-isometry-Metric-Space
                ( metric-space-proper-closed-interval-ℝ l1 [a,b])))))

  mul-ucont-map-proper-closed-interval-ℝ :
    ucont-map-proper-closed-interval-ℝ l1 (l2 ⊔ l3) [a,b]
  mul-ucont-map-proper-closed-interval-ℝ =
    ( map-mul-ucont-map-proper-closed-interval-ℝ ,
      is-ucont-map-mul-ucont-map-proper-closed-interval-ℝ)
```
