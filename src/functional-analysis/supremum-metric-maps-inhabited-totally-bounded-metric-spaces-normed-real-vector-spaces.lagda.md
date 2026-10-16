# The supremum metric on maps from inhabited, totally bounded metric spaces to normed real vector spaces

```agda
module functional-analysis.supremum-metric-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import functional-analysis.metric-abelian-group-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import group-theory.abelian-groups

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.metrics
open import metric-spaces.metrics-of-metric-spaces

open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

Given an
[inhabited, totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
`X` and a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, if
$\lVert f \rVert_X$ denotes the
[supremum](functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md)
of $\lVert f(x) \rVert$ for
[uniformly continuous](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
`f : X → V` over all `x : X`, then $f g ↦ \lVert f - g \rVert_X$ is a
[metric](metric-spaces.metrics-of-metric-spaces.md) on the
[metric space](functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md)
of such functions.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    metric-space-X→V =
      metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  (let
    uniformly-continuous-map-X→V =
      uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where

  sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-X→V → uniformly-continuous-map-X→V → ℝ⁰⁺ l4
  sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f g =
    sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( diff-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( f)
        ( g))
```

## Properties

### The supremum distance is a metric on the metric space of uniformly continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    metric-space-X→V =
      metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where abstract

  is-metric-sup-dist-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-metric-of-Metric-Space
      ( metric-space-X→V)
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  is-metric-sup-dist-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    d (f , _) (g , _) =
    is-least-upper-bound-is-supremum-family-ℝ
      ( λ x → dist-Normed-ℝ-Vector-Space V (f x) (g x))
      ( _)
      ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( _))
      ( real-ℚ⁺ d)
```

### The supremum distance is symmetric

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where abstract

  is-symmetric-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-symmetric-distance-function
      ( set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  is-symmetric-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    is-symmetric-is-metric-of-Metric-Space
      ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( is-metric-sup-dist-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
```

### The supremum distance is triangular

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where abstract

  is-triangular-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-triangular-distance-function
      ( set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  is-triangular-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    is-triangular-is-metric-of-Metric-Space
      ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( is-metric-sup-dist-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
```

### The supremum distance is extensional

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where abstract

  is-extensional-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-extensional-distance-function
      ( set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  is-extensional-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    is-extensional-is-metric-of-Metric-Space
      ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( is-metric-sup-dist-of-metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
```

### Zero laws of the supremum distance

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where abstract

  right-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (f :
      uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)) →
    sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( f)
      ( zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)) ＝
    sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( f)
  right-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f =
    ap
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( right-zero-law-right-subtraction-Ab
        ( ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V))
        ( f))

  left-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (f :
      uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)) →
    sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
      ( f) ＝
    sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( f)
  left-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f =
    ( is-symmetric-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( _)
      ( _)) ∙
    ( right-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( f))
```
