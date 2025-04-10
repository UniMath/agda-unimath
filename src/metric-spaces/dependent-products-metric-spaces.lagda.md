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

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A family of [metric spaces](metric-spaces.metric-spaces.md) over a type produces
a {{#concept "product metric space" Agda=Π-Metric-Space}} on the type of
dependent functions into the carrier types of the family. Two functions `f` and
`g` are in a [`d`-neighborhood](metric-spaces.premetric-structures.md) in the
product structure if this holds for all the evaluations `f x` and `g x`. I.e
this is the premetric such that
[upper bounds](metric-spaces.premetric-structures.md) on the distance between
`f` and `g` are bounded below by the supremum of the distances between each
`f x` and `g x`. The evaluation functions from the product metric space to each
projected metric space are
[short maps](metric-spaces.short-functions-metric-spaces.md).

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

  is-reflexive-structure-Π-Metric-Space :
    is-reflexive-Premetric structure-Π-Metric-Space
  is-reflexive-structure-Π-Metric-Space d f a =
    is-reflexive-structure-Metric-Space (P a) d (f a)

  is-symmetric-structure-Π-Metric-Space :
    is-symmetric-Premetric structure-Π-Metric-Space
  is-symmetric-structure-Π-Metric-Space d f g H a =
    is-symmetric-structure-Metric-Space (P a) d (f a) (g a) (H a)

  is-triangular-structure-Π-Metric-Space :
    is-triangular-Premetric structure-Π-Metric-Space
  is-triangular-structure-Π-Metric-Space f g h d₁ d₂ H K a =
    is-triangular-structure-Metric-Space
      ( P a)
      ( f a)
      ( g a)
      ( h a)
      ( d₁)
      ( d₂)
      ( H a)
      ( K a)

  is-local-structure-Π-Metric-Space :
    is-local-Premetric structure-Π-Metric-Space
  is-local-structure-Π-Metric-Space =
    is-local-is-tight-Premetric
      ( structure-Π-Metric-Space)
      ( λ f g H →
        eq-htpy
          ( λ a →
            is-tight-structure-Metric-Space
              ( P a)
              ( f a)
              ( g a)
              ( λ d → H d a)))

  is-pseudometric-structure-Π-Metric-Space :
    is-pseudometric-Premetric structure-Π-Metric-Space
  is-pseudometric-structure-Π-Metric-Space =
    is-reflexive-structure-Π-Metric-Space ,
    is-symmetric-structure-Π-Metric-Space ,
    is-triangular-structure-Π-Metric-Space

  is-metric-structure-Π-Metric-Space :
    is-metric-Premetric structure-Π-Metric-Space
  is-metric-structure-Π-Metric-Space =
    is-pseudometric-structure-Π-Metric-Space ,
    is-local-structure-Π-Metric-Space

  Π-Metric-Space : Metric-Space (l ⊔ l1) (l ⊔ l2)
  pr1 Π-Metric-Space = type-Π-Metric-Space , structure-Π-Metric-Space
  pr2 Π-Metric-Space = is-metric-structure-Π-Metric-Space
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

  short-ev-Π-Metric-Space :
    short-function-Metric-Space
      ( Π-Metric-Space A P)
      ( P a)
  short-ev-Π-Metric-Space = (λ f → f a) , (is-short-ev-Π-Metric-Space)
```

### The product of saturated metric spaces is saturated

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (Π-saturated : (a : A) → is-saturated-Metric-Space (P a))
  where

  is-saturated-Π-is-saturated-Metric-Space :
    is-saturated-Metric-Space (Π-Metric-Space A P)
  is-saturated-Π-is-saturated-Metric-Space ε x y H a =
    Π-saturated a ε (x a) (y a) (λ d → H d a)
```
