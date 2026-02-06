# The uniform limit theorem in metric spaces

```agda
module metric-spaces.uniform-limit-theorem-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.ternary-sum-decompositions-positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

The
{{#concept "uniform limit theorem" WDID=Q7885107 WD="uniform limit theorem" Agda=is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-Metric-Space}}
states that uniform convergence of a sequence of
[maps between metric spaces](metric-spaces.maps-metric-spaces.md), i.e.,
convergence in the
[metric space of maps](metric-spaces.metric-space-of-maps-metric-spaces.md),
preserves
[pointwise ε-δ continuity](metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces.md)
Assuming the
[axiom of countable choice](foundation.axiom-of-countable-choice.md), this also
yields
[pointwise continuity](metric-spaces.pointwise-continuous-maps-metric-spaces.md).

## Properties

### The uniform limit theorem for pointwise ε-δ continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-ε-δ-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-ε-δ-continuous-map-Metric-Space X Y f
    is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-Metric-Space
      L H x ε =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ( ℚ⁺)
                ( λ δ →
                  Π-Prop
                    ( type-Metric-Space X)
                    ( λ x' →
                      neighborhood-prop-Metric-Space X δ x x' ⇒
                      neighborhood-prop-Metric-Space Y ε (f x) (f x'))))
      in do
        (m , is-mod-m) ← L
        let
          ε₁ = left-summand-ternary-sum-decomposition-ℚ⁺ ε
          ε₂ = middle-summand-ternary-sum-decomposition-ℚ⁺ ε
          ε₃ = right-summand-ternary-sum-decomposition-ℚ⁺ ε
          ε₁₃ = min-ℚ⁺ ε₁ ε₃
          N = m ε₁₃

          uniform-min :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₁₃ (u N x) (f x)
          uniform-min =
            is-modulus-limit-modulus-sequence-Metric-Space
              ( metric-space-of-maps-Metric-Space X Y)
              ( u)
              ( f)
              ( m , is-mod-m)
              ( ε₁₃)
              ( N)
              ( refl-leq-ℕ N)

          uniform-left :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₁ (u N x) (f x)
          uniform-left x =
            weakly-monotonic-neighborhood-Metric-Space
              ( Y)
              ( u N x)
              ( f x)
              ( ε₁₃)
              ( ε₁)
              ( leq-left-min-ℚ⁺ ε₁ ε₃)
              ( uniform-min x)

          uniform-right :
            (x : type-Metric-Space X) →
            neighborhood-Metric-Space Y ε₃ (u N x) (f x)
          uniform-right x =
            weakly-monotonic-neighborhood-Metric-Space
              ( Y)
              ( u N x)
              ( f x)
              ( ε₁₃)
              ( ε₃)
              ( leq-right-min-ℚ⁺ ε₁ ε₃)
              ( uniform-min x)
        (δ , is-mod-δ) ← H N x ε₂
        intro-exists
          ( δ)
          ( λ x' Nx' →
            tr
              ( is-upper-bound-dist-Metric-Space Y (f x) (f x'))
              ( eq-add-ternary-sum-decomposition-ℚ⁺ ε)
              ( triangular-neighborhood-Metric-Space
                ( Y)
                ( f x)
                ( u N x')
                ( f x')
                ( ε₁ +ℚ⁺ ε₂)
                ( ε₃)
                ( uniform-right x')
                ( triangular-neighborhood-Metric-Space
                  ( Y)
                  ( f x)
                  ( u N x)
                  ( u N x')
                  ( ε₁)
                  ( ε₂)
                  ( is-mod-δ x' Nx')
                  ( symmetric-neighborhood-Metric-Space
                    ( Y)
                    ( ε₁)
                    ( u N x)
                    ( f x)
                    ( uniform-left x)))))
```

### Uniform limits of pointwise continuous maps are ε-δ continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-pointwise-continuous-map-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-ε-δ-continuous-map-Metric-Space X Y f
    is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-pointwise-continuous-map-Metric-Space
      L H =
      is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-Metric-Space
        ( X)
        ( Y)
        ( u)
        ( f)
        ( L)
        ( λ n →
          is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-Metric-Space
            ( X)
            ( Y)
            ( u n , H n))
```

### Uniform limits of pointwise continuous maps are pointwise continuous, assuming the axiom of countable choice

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acω : level-choice-ℕ (l1 ⊔ l2 ⊔ l4))
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (u : sequence (map-Metric-Space X Y))
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-continuous-map-uniform-limit-sequence-choice-ℕ-Metric-Space :
      is-limit-sequence-Metric-Space
        ( metric-space-of-maps-Metric-Space X Y)
        ( u)
        ( f) →
      ( (n : ℕ) → is-pointwise-continuous-map-Metric-Space X Y (u n)) →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-map-uniform-limit-sequence-choice-ℕ-Metric-Space
      L H =
      is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-choice-ℕ-Metric-Space
        ( acω)
        ( X)
        ( Y)
        ( f)
        ( is-pointwise-ε-δ-continuous-map-uniform-limit-sequence-pointwise-continuous-map-Metric-Space
          ( X)
          ( Y)
          ( u)
          ( f)
          ( L)
          ( H))
```
