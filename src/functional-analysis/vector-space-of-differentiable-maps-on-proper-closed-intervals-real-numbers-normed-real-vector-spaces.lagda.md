# The vector space of differentiable maps from proper closed intervals in ℝ to normed real vector spaces

```agda
module functional-analysis.vector-space-of-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import functional-analysis.addition-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces
open import functional-analysis.differentiability-constant-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces
open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces
open import functional-analysis.scalar-multiplication-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.function-real-vector-spaces
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.subspaces-vector-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.field-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
```

</details>

## Idea

Given a [normed real vector space](linear-algebra.normed-real-vector-spaces.md)
`V` and a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]`, the
[differentiable](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces.md)
maps from `[a, b]` to `V` form a
[subspace](linear-algebra.subspaces-vector-spaces.md) of all maps from `[a, b]`
to `V`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  abstract
    is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( const
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( zero-Normed-ℝ-Vector-Space V))
    is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      is-differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( zero-Normed-ℝ-Vector-Space V)

    is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      (f g :
        type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V) →
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f) →
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( g) →
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( λ x → add-Normed-ℝ-Vector-Space V (f x) (g x))
    is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      f g Df Dg =
      is-differentiable-map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f , Df)
        ( g , Dg)

    is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      (c : ℝ l1)
      (f :
        type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V) →
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f) →
      is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( λ x → mul-Normed-ℝ-Vector-Space V c (f x))
    is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      c f Df =
      is-differentiable-map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( c)
        ( f , Df)

  is-subspace-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-subspace-Vector-Space
      ( heyting-field-ℝ l1)
      ( function-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( type-proper-closed-interval-ℝ l1 [a,b]))
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]))
  is-subspace-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( is-differentiable-const-zero-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-closed-under-addition-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-closed-under-scalar-multiplication-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  subspace-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    subspace-Vector-Space
      ( lsuc l1 ⊔ l2)
      ( heyting-field-ℝ l1)
      ( function-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( type-proper-closed-interval-ℝ l1 [a,b]))
  subspace-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]) ,
      is-subspace-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    ℝ-Vector-Space l1 (lsuc l1 ⊔ l2)
  vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    vector-space-subspace-Vector-Space
      ( heyting-field-ℝ l1)
      ( function-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( type-proper-closed-interval-ℝ l1 [a,b]))
      ( subspace-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```

## Properties

### The derivative operation is a linear map from the space of differentiable functions to the space of functions

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  abstract
    is-additive-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-additive-map-Vector-Space
        ( heyting-field-ℝ l1)
        ( vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b]))
        ( function-ℝ-Vector-Space
          ( vector-space-Normed-ℝ-Vector-Space V)
          ( type-proper-closed-interval-ℝ l1 [a,b]))
        ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b]))
    is-additive-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      _ _ =
      refl

    is-homogeneous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-homogeneous-map-Vector-Space
        ( heyting-field-ℝ l1)
        ( vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b]))
        ( function-ℝ-Vector-Space
          ( vector-space-Normed-ℝ-Vector-Space V)
          ( type-proper-closed-interval-ℝ l1 [a,b]))
        ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b]))
    is-homogeneous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      _ _ =
      refl

  is-linear-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-linear-map-Vector-Space
      ( heyting-field-ℝ l1)
      ( vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]))
      ( function-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( type-proper-closed-interval-ℝ l1 [a,b]))
      ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]))
  is-linear-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( is-additive-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-homogeneous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  linear-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    linear-map-Vector-Space
      ( heyting-field-ℝ l1)
      ( vector-space-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]))
      ( function-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( type-proper-closed-interval-ℝ l1 [a,b]))
  linear-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]) ,
      is-linear-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```
