# The metric space of convergent Cauchy approximations in a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[convergent Cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) inherits the
[metric substructure](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of Cauchy approximations](metric-spaces.metric-space-of-cauchy-approximations-metric-spaces.md).
This is the
{{#concept "metric space of convergent Cauchy approximations" Disambiguation="in a metric space" Agda=metric-space-of-convergent-cauchy-approximations-Metric-Space}}
in a metric space.

## Definitions

### The metric space of Cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  metric-space-of-convergent-cauchy-approximations-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-of-convergent-cauchy-approximations-Metric-Space =
    subspace-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( is-convergent-prop-cauchy-approximation-Metric-Space A)
```

## Properties

### The map from a convergent Cauchy approximation in `M` to its limit is a short map into the saturated metric space of `M`

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-short-saturated-limit-convergent-cauchy-approximation-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space A)
      ( saturate-Metric-Space A)
      ( limit-convergent-cauchy-approximation-Metric-Space A)
  is-short-saturated-limit-convergent-cauchy-approximation-Metric-Space
    ε x y Nxy δ =
    tr
      ( λ d →
        neighborhood-Metric-Space A d
          ( limit-convergent-cauchy-approximation-Metric-Space A x)
          ( limit-convergent-cauchy-approximation-Metric-Space A y))
      ( lemma-ε-δ-θ-η)
      ( lemma-neighborhood-limit θ η η')
    where

    lemma-neighborhood-limit :
      (θ η η' : ℚ⁺) →
      neighborhood-Metric-Space
        ( A)
        ( (θ +ℚ⁺ η) +ℚ⁺ ε +ℚ⁺ (θ +ℚ⁺ η'))
        ( limit-convergent-cauchy-approximation-Metric-Space A x)
        ( limit-convergent-cauchy-approximation-Metric-Space A y)
    lemma-neighborhood-limit θ η η' =
      is-triangular-structure-Metric-Space
        ( A)
        ( limit-convergent-cauchy-approximation-Metric-Space A x)
        ( map-convergent-cauchy-approximation-Metric-Space A y θ)
        ( limit-convergent-cauchy-approximation-Metric-Space A y)
        ( θ +ℚ⁺ η +ℚ⁺ ε)
        ( θ +ℚ⁺ η')
        ( is-limit-limit-convergent-cauchy-approximation-Metric-Space A y θ η')
        ( is-triangular-structure-Metric-Space
          ( A)
          ( limit-convergent-cauchy-approximation-Metric-Space A x)
          ( map-convergent-cauchy-approximation-Metric-Space A x θ)
          ( map-convergent-cauchy-approximation-Metric-Space A y θ)
          ( θ +ℚ⁺ η)
          ( ε)
          ( Nxy θ)
          ( is-symmetric-structure-Metric-Space
            ( A)
            ( θ +ℚ⁺ η)
            ( map-convergent-cauchy-approximation-Metric-Space A x θ)
            ( limit-convergent-cauchy-approximation-Metric-Space A x)
            ( is-limit-limit-convergent-cauchy-approximation-Metric-Space
              ( A)
              ( x)
              ( θ)
              ( η))))

    δ₁ : ℚ⁺
    δ₁ = left-summand-split-ℚ⁺ δ

    δ₂ : ℚ⁺
    δ₂ = right-summand-split-ℚ⁺ δ

    δₘ : ℚ⁺
    δₘ = mediant-zero-min-ℚ⁺ δ₁ δ₂

    θ : ℚ⁺
    θ = modulus-le-double-le-ℚ⁺ δₘ

    θ<δ₁ : le-ℚ⁺ θ δ₁
    θ<δ₁ =
      transitive-le-ℚ⁺ θ δₘ δ₁
        ( le-left-mediant-zero-min-ℚ⁺ δ₁ δ₂)
        ( le-modulus-le-double-le-ℚ⁺ δₘ)

    θ<δ₂ : le-ℚ⁺ θ δ₂
    θ<δ₂ =
      transitive-le-ℚ⁺ θ δₘ δ₂
        ( le-right-mediant-zero-min-ℚ⁺ δ₁ δ₂)
        ( le-modulus-le-double-le-ℚ⁺ δₘ)

    η : ℚ⁺
    η = le-diff-ℚ⁺ θ δ₁ θ<δ₁

    η' : ℚ⁺
    η' = le-diff-ℚ⁺ θ δ₂ θ<δ₂

    lemma-ε-δ-θ-η :
      ((θ +ℚ⁺ η) +ℚ⁺ ε +ℚ⁺ (θ +ℚ⁺ η')) ＝ ε +ℚ⁺ δ
    lemma-ε-δ-θ-η =
      ( ap-binary
        ( λ u v → u +ℚ⁺ ε +ℚ⁺ v)
        ( right-diff-law-add-ℚ⁺ θ δ₁ θ<δ₁)
        ( right-diff-law-add-ℚ⁺ θ δ₂ θ<δ₂)) ∙
      ( ap (add-ℚ⁺' δ₂) (commutative-add-ℚ⁺ δ₁ ε)) ∙
      ( associative-add-ℚ⁺ ε δ₁ δ₂) ∙
      ( ap (add-ℚ⁺ ε) (eq-add-split-ℚ⁺ δ))
```

### The map from a convergent Cauchy approximation in a saturated metric to its limit is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (is-saturated : is-saturated-Metric-Space A)
  where

  is-short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space A)
      ( A)
      ( limit-convergent-cauchy-approximation-Metric-Space A)
  is-short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space
    ε x y Nxy =
    is-saturated
      ( ε)
      ( limit-convergent-cauchy-approximation-Metric-Space A x)
      ( limit-convergent-cauchy-approximation-Metric-Space A y)
      ( is-short-saturated-limit-convergent-cauchy-approximation-Metric-Space
        ( A)
        ( ε)
        ( x)
        ( y)
        ( Nxy))

  short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space :
    short-function-Metric-Space
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space A)
      ( A)
  short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space =
    limit-convergent-cauchy-approximation-Metric-Space A ,
    is-short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space
```
