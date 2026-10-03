# The supremum norm on maps from inhabited totally bounded metric spaces to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.supremum-norm-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import functional-analysis.metric-abelian-group-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.real-vector-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.supremum-metric-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import group-theory.abelian-groups

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.seminormed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.suprema-families-nonnegative-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

Given an
[inhabited totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
`X` and a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, the
[uniformly continuous maps](functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md)
`f : X → V` form a normed real vector space under the
[supremum norm](functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md).

## Proof

### The supremum norm is preserved by negation

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    ab-X→V =
      ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
    uniformly-continuous-map-X→V = type-Ab ab-X→V
    neg-X→V = neg-Ab ab-X→V
    sup-norm-X→V =
      sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where abstract

  sup-norm-neg-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (f : uniformly-continuous-map-X→V) →
    sup-norm-X→V (neg-X→V f) ＝ sup-norm-X→V f
  sup-norm-neg-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f@(map-f , _) =
    eq-is-supremum-family-ℝ⁰⁺
      ( λ x → nonnegative-norm-Normed-ℝ-Vector-Space V (map-f x))
      ( sup-norm-X→V (neg-X→V f))
      ( tr
        ( λ g → is-supremum-family-ℝ⁰⁺ g (sup-norm-X→V (neg-X→V f)))
        ( eq-htpy
          ( λ x → nonnegative-norm-neg-Normed-ℝ-Vector-Space V (map-f x)))
        ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V)
          ( neg-X→V f)))
      ( sup-norm-X→V f)
      ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( f))
```

### The supremum norm is triangular

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    ab-X→V =
      ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
    uniformly-continuous-map-X→V = type-Ab ab-X→V
    _+X→V_ = add-Ab ab-X→V
    _-X→V_ = right-subtraction-Ab ab-X→V
    neg-X→V = neg-Ab ab-X→V
    0-X→V = zero-Ab ab-X→V
    sup-norm-X→V =
      sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where abstract

  is-triangular-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (f g : uniformly-continuous-map-X→V) →
    leq-ℝ⁰⁺
      ( sup-norm-X→V (f +X→V g))
      ( sup-norm-X→V f +ℝ⁰⁺ sup-norm-X→V g)
  is-triangular-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f g =
    binary-tr
      ( leq-ℝ⁰⁺)
      ( ap (λ h → sup-norm-X→V (f +X→V h)) (neg-neg-Ab ab-X→V g))
      ( ap-add-ℝ⁰⁺
        ( right-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V)
          ( f))
        ( ( left-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
            ( X)
            ( V)
            ( _)) ∙
          ( sup-norm-neg-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
            ( X)
            ( V)
            ( g))))
      ( is-triangular-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( f)
        ( 0-X→V)
        ( neg-X→V g))
```

### The supremum norm is absolutely homogeneous

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    uniformly-continuous-map-X→V =
      uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
    _ℝ*X→V_ =
      scalar-mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
    sup-norm-X→V =
      sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where abstract

  is-absolutely-homogeneous-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (c : ℝ l4) (f : uniformly-continuous-map-X→V) →
    sup-norm-X→V (c ℝ*X→V f) ＝ nonnegative-abs-ℝ c *ℝ⁰⁺ sup-norm-X→V f
  is-absolutely-homogeneous-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    c f@(map-f , _) =
    eq-is-supremum-family-ℝ⁰⁺
      ( λ x →
        nonnegative-norm-Normed-ℝ-Vector-Space V
          ( mul-Normed-ℝ-Vector-Space V c (map-f x)))
      ( sup-norm-X→V (c ℝ*X→V f))
      ( is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
        ( c ℝ*X→V f))
      ( nonnegative-abs-ℝ c *ℝ⁰⁺ sup-norm-X→V f)
      ( inv-tr
        ( λ g →
          is-supremum-family-ℝ⁰⁺ g (nonnegative-abs-ℝ c *ℝ⁰⁺ sup-norm-X→V f))
        ( eq-htpy
          ( λ x →
            eq-ℝ⁰⁺ _ _
              ( is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space
                ( V)
                ( c)
                ( map-f x))))
        ( is-supremum-mul-sup-has-supremum-family-ℝ⁰⁺
          ( nonnegative-norm-Normed-ℝ-Vector-Space V ∘ map-f)
          ( nonnegative-abs-ℝ c)
          ( has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
            ( X)
            ( V)
            ( f))))
```

### The supremum norm is extensional

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    ab-X→V =
      ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V)
    uniformly-continuous-map-X→V = type-Ab ab-X→V
    0-X→V = zero-Ab ab-X→V
    sup-norm-X→V =
      sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where abstract

  is-extensional-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    (f : uniformly-continuous-map-X→V) →
    is-zero-ℝ (real-ℝ⁰⁺ (sup-norm-X→V f)) →
    f ＝ 0-X→V
  is-extensional-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
    f |f|=0 =
    is-extensional-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
      ( f)
      ( 0-X→V)
      ( inv-tr
        ( is-zero-ℝ ∘ real-ℝ⁰⁺)
        ( right-zero-law-sup-dist-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
          ( X)
          ( V)
          ( f))
        ( |f|=0))
```

### The normed real vector space of uniformly continuous maps from inhabited, totally bounded metric spaces to normed real vector spaces

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where

  seminorm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    seminorm-ℝ-Vector-Space
      ( vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  seminorm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    ( real-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V) ,
      is-triangular-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V) ,
      λ c f →
        ap
          ( real-ℝ⁰⁺)
          ( is-absolutely-homogeneous-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
            ( X)
            ( V)
            ( c)
            ( f)))

  norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    norm-ℝ-Vector-Space
      ( vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    ( seminorm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space ,
      is-extensional-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))

  normed-vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Normed-ℝ-Vector-Space l4 (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  normed-vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    ( vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V) ,
      norm-sup-norm-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```
