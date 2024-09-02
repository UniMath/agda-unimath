# Dependent products of metric spaces

```agda
module metric-spaces.dependent-products-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A family of [metric spaces](metric-spaces.metric-spaces.md) over a type produces
a {{#concept "product metric space" Agda=Π-Metric-Space}} on the type of
dependent functions into the carrier types of the family. Two functions `f` and
`g` are in a [`d`-neighbourhood](metric-spaces.premetric-structures.md) in the
product structure if this holds for all the evaluations `f x` and `g x`.

The evaluation functions from the product metric space to each projected metric
space are [short maps](metric-spaces.short-functions-metric-spaces.md).

## Definitions

### Product of metric spaces

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  where

  type-Π-Metric-Space : UU (l ⊔ l1)
  type-Π-Metric-Space = (x : A) → type-Metric-Space (P x)

  structure-Π-Metric-Space : Premetric (l ⊔ l2) type-Π-Metric-Space
  structure-Π-Metric-Space d f g =
    Π-Prop A (λ x → structure-Metric-Space (P x) d (f x) (g x))

  Π-Metric-Space : Metric-Space (l ⊔ l1) (l ⊔ l2)
  pr1 (pr1 Π-Metric-Space) = type-Π-Metric-Space
  pr2 (pr1 Π-Metric-Space) = structure-Π-Metric-Space
  pr2 Π-Metric-Space =
    ( λ d f a →
      is-reflexive-premetric-structure-Metric-Space
        ( P a)
        ( d)
        ( f a)) ,
    ( λ d f g H a →
      is-symmetric-premetric-structure-Metric-Space
        ( P a)
        ( d)
        ( f a)
        ( g a)
        ( H a)) ,
    ( is-local-is-tight-Premetric
      ( structure-Π-Metric-Space)
      ( λ f g H →
        eq-htpy
          ( λ a →
            is-tight-premetric-structure-Metric-Space
              ( P a)
              ( f a)
              ( g a)
              ( λ d → H d a)))) ,
    ( λ f g h d₁ d₂ H K a →
      is-triangular-premetric-structure-Metric-Space
        ( P a)
        ( f a)
        ( g a)
        ( h a)
        ( d₁)
        ( d₂)
        ( H a)
        ( K a))
```

## Properties

### The evaluation maps on a product metric space are short

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2) (a : A)
  where

  is-short-ev-Π-Metric-Space :
    is-short-function-Metric-Space
      ( Π-Metric-Space A P)
      ( P a)
      ( λ f → f a)
  is-short-ev-Π-Metric-Space ε x y H = H a
```
