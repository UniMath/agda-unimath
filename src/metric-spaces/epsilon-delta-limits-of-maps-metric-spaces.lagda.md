# ε-δ limits of maps between metric spaces

```agda
module metric-spaces.epsilon-delta-limits-of-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.limits-of-maps-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The
{{#concept "ε-δ definition of a limit" WDID=Q1042034 WD="(ε, δ)-definition of limit" Disambiguation="in a metric space" Agda=is-ε-δ-limit-map-Metric-Space}}
states that the limit of `f x` as `x` approaches `x₀` is a `y` such that for any
`ε : ℚ⁺`, there [exists](foundation.existential-quantification.md) a `δ : ℚ⁺`
such that if `x` and `x₀` are in a `δ`-neighborhood of each other, `f x` and `y`
are in an `ε`-neighborhood of each other.

This contrasts to the definition of a
[limit](metric-spaces.limits-of-maps-metric-spaces.md) of a map in a metric
space, where there must exist a modulus map `μ : ℚ⁺ → ℚ⁺` assigning an
appropriate `δ` for each possible value of `ε`. A limit is an ε-δ limit, but the
converse requires the
[axiom of countable choice](foundation.axiom-of-countable-choice.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  (x : type-Metric-Space X)
  (y : type-Metric-Space Y)
  where

  is-ε-δ-limit-prop-map-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-ε-δ-limit-prop-map-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        ∃ ( ℚ⁺)
          ( λ δ →
            Π-Prop
              ( type-Metric-Space X)
              ( λ x' →
                neighborhood-prop-Metric-Space X δ x x' ⇒
                neighborhood-prop-Metric-Space Y ε y (f x'))))

  is-ε-δ-limit-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-ε-δ-limit-map-Metric-Space =
    type-Prop is-ε-δ-limit-prop-map-Metric-Space
```

## Properties

### Limits are ε-δ limits

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  (x : type-Metric-Space X)
  (y : type-Metric-Space Y)
  where

  abstract
    is-ε-δ-limit-is-limit-map-Metric-Space :
      is-point-limit-map-Metric-Space X Y f x y →
      is-ε-δ-limit-map-Metric-Space X Y f x y
    is-ε-δ-limit-is-limit-map-Metric-Space H ε =
      map-trunc-Prop (λ (μ , is-mod-μ) → (μ ε , is-mod-μ ε)) H
```

### Assuming countable choice, ε-δ limits are limits

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acω : ACω)
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  (x : type-Metric-Space X)
  (y : type-Metric-Space Y)
  where

  abstract
    is-limit-is-ε-δ-limit-map-ACω-Metric-Space :
      is-ε-δ-limit-map-Metric-Space X Y f x y →
      is-point-limit-map-Metric-Space X Y f x y
    is-limit-is-ε-δ-limit-map-ACω-Metric-Space H =
      let
        open
          do-syntax-trunc-Prop
            ( is-point-limit-prop-map-Metric-Space X Y f x y)
      in do
        μ ←
          choice-countable-discrete-set-ACω
            ( set-ℚ⁺)
            ( is-countable-set-ℚ⁺)
            ( has-decidable-equality-ℚ⁺)
            ( acω)
            ( λ ε →
              Σ-Set
                ( set-ℚ⁺)
                ( λ δ →
                  set-Prop
                    ( Π-Prop
                      ( type-Metric-Space X)
                      ( λ x' →
                        neighborhood-prop-Metric-Space X δ x x' ⇒
                        neighborhood-prop-Metric-Space Y ε y (f x')))))
            ( H)
        intro-exists (pr1 ∘ μ) (pr2 ∘ μ)
```

## See also

- [Limits of maps in metric spaces](metric-spaces.limits-of-maps-metric-spaces.md)
