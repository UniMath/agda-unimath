# Similarity relation on Cauchy approximations in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.similarity-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.sublinear-rational-cauchy-approximations

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
open import metric-spaces.rational-cauchy-approximations-of-zero
open import metric-spaces.short-functions-metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

Two
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
`f` and `g` in a [metric space](metric-spaces.metric-spaces.md) are
{{#concept "similar" Disambiguation="Cauchy approximations in a metric space" Agda=sim-cauchy-approximation-Metric-Space}}
if `f ε` and `g δ` are `(ε + δ + θ)`-neighborhs for all `(ε δ θ : ℚ⁺)`.

## Definitions

### Similarity of Cauchy approximations

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f g : cauchy-approximation-Metric-Space A)
  where

  sim-prop-cauchy-approximation-Metric-Space : Prop l2
  sim-prop-cauchy-approximation-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            Π-Prop
              ( ℚ⁺)
              ( λ θ →
                structure-Metric-Space
                  ( A)
                  ( ε +ℚ⁺ δ +ℚ⁺ θ)
                  ( map-cauchy-approximation-Metric-Space A f ε)
                  ( map-cauchy-approximation-Metric-Space A g δ))))

  sim-cauchy-approximation-Metric-Space : UU l2
  sim-cauchy-approximation-Metric-Space =
    type-Prop sim-prop-cauchy-approximation-Metric-Space
```

## Properties

### Any Cauchy approximation is similar to itself

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  abstract
    refl-sim-cauchy-approximation-Metric-Space :
      sim-cauchy-approximation-Metric-Space A f f
    refl-sim-cauchy-approximation-Metric-Space ε δ θ =
      is-monotonic-structure-Metric-Space
        ( A)
        ( map-cauchy-approximation-Metric-Space A f ε)
        ( map-cauchy-approximation-Metric-Space A f δ)
        ( ε +ℚ⁺ δ)
        ( ε +ℚ⁺ δ +ℚ⁺ θ)
        ( le-left-add-ℚ⁺ (ε +ℚ⁺ δ) θ)
        ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space A f ε δ)
```

### Similarity of Cauchy approximations is symmetric

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f g : cauchy-approximation-Metric-Space A)
  where

  abstract
    symmetric-sim-cauchy-approximation-Metric-Space :
      sim-cauchy-approximation-Metric-Space A f g →
      sim-cauchy-approximation-Metric-Space A g f
    symmetric-sim-cauchy-approximation-Metric-Space H ε δ θ =
      tr
        ( is-upper-bound-dist-Metric-Space
          ( A)
          (map-cauchy-approximation-Metric-Space A g ε)
          (map-cauchy-approximation-Metric-Space A f δ))
        ( ap (add-ℚ⁺' θ) (commutative-add-ℚ⁺ δ ε))
        ( is-symmetric-structure-Metric-Space
          ( A)
          ( δ +ℚ⁺ ε +ℚ⁺ θ)
          ( map-cauchy-approximation-Metric-Space A f δ)
          ( map-cauchy-approximation-Metric-Space A g ε)
          ( H δ ε θ))
```

### Similarity of Cauchy approximation is transitive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f g h : cauchy-approximation-Metric-Space A)
  where

  abstract
    transitive-sim-cauchy-approximation-Metric-Space :
      sim-cauchy-approximation-Metric-Space A g h →
      sim-cauchy-approximation-Metric-Space A f g →
      sim-cauchy-approximation-Metric-Space A f h
    transitive-sim-cauchy-approximation-Metric-Space g~h f~g ε δ θ =
      tr
        ( is-upper-bound-dist-Metric-Space
          ( A)
          ( map-cauchy-approximation-Metric-Space A f ε)
          ( map-cauchy-approximation-Metric-Space A h δ))
        ( eq-εδθ)
        ( is-triangular-structure-Metric-Space
          ( A)
          ( map-cauchy-approximation-Metric-Space A f ε)
          ( map-cauchy-approximation-Metric-Space A g θ₀)
          ( map-cauchy-approximation-Metric-Space A h δ)
          ( ε +ℚ⁺ θ₀ +ℚ⁺ θ₁')
          ( δ +ℚ⁺ θ₀ +ℚ⁺ θ₂')
          ( tr
            ( λ x →
              is-upper-bound-dist-Metric-Space
                ( A)
                ( map-cauchy-approximation-Metric-Space A g θ₀)
                ( map-cauchy-approximation-Metric-Space A h δ)
                ( x +ℚ⁺ θ₂'))
            ( commutative-add-ℚ⁺ θ₀ δ)
            ( g~h θ₀ δ θ₂'))
          ( f~g ε θ₀ θ₁'))
      where

      θ₁ θ₂ θ₀ θ₁' θ₂' : ℚ⁺
      θ₁ = left-summand-split-ℚ⁺ θ
      θ₂ = right-summand-split-ℚ⁺ θ
      θ₀ = mediant-zero-min-ℚ⁺ θ₁ θ₂
      θ₁' = le-diff-ℚ⁺ θ₀ θ₁ (le-left-mediant-zero-min-ℚ⁺ θ₁ θ₂)
      θ₂' = le-diff-ℚ⁺ θ₀ θ₂ (le-right-mediant-zero-min-ℚ⁺ θ₁ θ₂)

      eq-θ₁ : θ₀ +ℚ⁺ θ₁' ＝ θ₁
      eq-θ₁ = right-diff-law-add-ℚ⁺ θ₀ θ₁ (le-left-mediant-zero-min-ℚ⁺ θ₁ θ₂)

      eq-θ₂ : θ₀ +ℚ⁺ θ₂' ＝ θ₂
      eq-θ₂ = right-diff-law-add-ℚ⁺ θ₀ θ₂ (le-right-mediant-zero-min-ℚ⁺ θ₁ θ₂)

      eq-εδθ :
        (ε +ℚ⁺ θ₀ +ℚ⁺ θ₁') +ℚ⁺ (δ +ℚ⁺ θ₀ +ℚ⁺ θ₂') ＝
        (ε +ℚ⁺ δ +ℚ⁺ θ)
      eq-εδθ =
        ( ap-binary
          ( add-ℚ⁺)
          ( ( associative-add-ℚ⁺ ε θ₀ θ₁') ∙ (ap (add-ℚ⁺ ε) eq-θ₁))
          ( (associative-add-ℚ⁺ δ θ₀ θ₂') ∙ (ap (add-ℚ⁺ δ) eq-θ₂))) ∙
        ( interchange-law-add-add-ℚ⁺ ε θ₁ δ θ₂) ∙
        ( ap (add-ℚ⁺ (ε +ℚ⁺ δ)) (eq-add-split-ℚ⁺ θ))
```

### A Cauchy approximation is convergent if and only if it is similar to a constant map

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A) (x : type-Metric-Space A)
  where

  sim-const-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    sim-cauchy-approximation-Metric-Space
      ( A)
      ( f)
      ( const-cauchy-approximation-Metric-Space A x)
  sim-const-is-limit-cauchy-approximation-Metric-Space lim-f-x ε δ θ =
    inv-tr
      ( is-upper-bound-dist-Metric-Space
        ( A)
        ( map-cauchy-approximation-Metric-Space A f ε)
        ( x))
      ( associative-add-ℚ⁺ ε δ θ)
      ( lim-f-x ε (δ +ℚ⁺ θ))

  is-limit-sim-const-cauchy-approximation-Metric-Space :
    sim-cauchy-approximation-Metric-Space
      ( A)
      ( f)
      ( const-cauchy-approximation-Metric-Space A x) →
    is-limit-cauchy-approximation-Metric-Space A f x
  is-limit-sim-const-cauchy-approximation-Metric-Space H ε δ =
    tr
      ( is-upper-bound-dist-Metric-Space
        ( A)
        ( map-cauchy-approximation-Metric-Space A f ε)
        ( x))
      ( ( associative-add-ℚ⁺
          ( ε)
          ( left-summand-split-ℚ⁺ δ)
          ( right-summand-split-ℚ⁺ δ)) ∙
        ( ap (add-ℚ⁺ ε) (eq-add-split-ℚ⁺ δ)))
      ( H ε (left-summand-split-ℚ⁺ δ) (right-summand-split-ℚ⁺ δ))
```

### Similarity of Cauchy approximations preserves limits

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f g : cauchy-approximation-Metric-Space A)
  (f~g : sim-cauchy-approximation-Metric-Space A f g)
  (x : type-Metric-Space A)
  where

  preserves-limit-sim-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A g x
  preserves-limit-sim-cauchy-approximation-Metric-Space H =
    is-limit-sim-const-cauchy-approximation-Metric-Space
      ( A)
      ( g)
      ( x)
      ( transitive-sim-cauchy-approximation-Metric-Space
        ( A)
        ( g)
        ( f)
        ( const-cauchy-approximation-Metric-Space A x)
        ( sim-const-is-limit-cauchy-approximation-Metric-Space A f x H)
        ( symmetric-sim-cauchy-approximation-Metric-Space A f g f~g))
```
