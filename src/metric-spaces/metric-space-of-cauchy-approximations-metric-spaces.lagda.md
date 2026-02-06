# The metric space of Cauchy approximations in a metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.involutions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a [metric space](metric-spaces.metric-spaces.md) `A` inherits the
[metric substructure](metric-spaces.subspaces-metric-spaces.md) of the constant
[product structure](metric-spaces.dependent-products-metric-spaces.md) over `A`.

This is the
{{#concept "metric space of Cauchy approximations" Disambiguation="in a metric space" Agda=metric-space-of-cauchy-approximations-Metric-Space}}
in a metric space.

## Definitions

### The metric space of Cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  metric-space-of-cauchy-approximations-Metric-Space : Metric-Space (l1 ⊔ l2) l2
  metric-space-of-cauchy-approximations-Metric-Space =
    subspace-Metric-Space
      ( Π-Metric-Space ℚ⁺ (λ _ → A))
      ( is-cauchy-approximation-prop-Metric-Space A)
```

## Properties

### The map `(x : A) ↦ const x` is an isometry between `A` and the metric space of cauchy approximations in `A`

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-isometry-const-cauchy-approximation-Metric-Space :
    is-isometry-Metric-Space
      ( A)
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( const-cauchy-approximation-Metric-Space A)
  is-isometry-const-cauchy-approximation-Metric-Space ε x y =
    ( λ Nxy η → Nxy) ,
    ( λ Nxy → Nxy one-ℚ⁺)

  isometry-const-cauchy-approximation-Metric-Space :
    isometry-Metric-Space
      ( A)
      ( metric-space-of-cauchy-approximations-Metric-Space A)
  isometry-const-cauchy-approximation-Metric-Space =
    ( const-cauchy-approximation-Metric-Space A ,
      is-isometry-const-cauchy-approximation-Metric-Space)
```

### Swapping the arguments of a Cauchy approximation of Cauchy approximations produces a Cauchy approximation

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  ( U : cauchy-approximation-Metric-Space
    ( metric-space-of-cauchy-approximations-Metric-Space A))
  where

  map-swap-map-cauchy-approximation-Metric-Space :
    ℚ⁺ → ℚ⁺ → type-Metric-Space A
  map-swap-map-cauchy-approximation-Metric-Space η ε =
    map-cauchy-approximation-Metric-Space
      ( A)
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A)
        ( U)
        ( ε))
      ( η)

  is-cauchy-map-swap-map-cauchy-approximation-Metric-Space :
    (η : ℚ⁺) →
    is-cauchy-approximation-Metric-Space
      ( A)
      ( map-swap-map-cauchy-approximation-Metric-Space η)
  is-cauchy-map-swap-map-cauchy-approximation-Metric-Space η ε δ =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( U)
      ( ε)
      ( δ)
      ( η)

  map-swap-cauchy-approximation-Metric-Space :
    ℚ⁺ → cauchy-approximation-Metric-Space A
  map-swap-cauchy-approximation-Metric-Space η =
    ( map-swap-map-cauchy-approximation-Metric-Space η ,
      is-cauchy-map-swap-map-cauchy-approximation-Metric-Space η)

  is-cauchy-map-swap-cauchy-approximation-Metric-Space :
    is-cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( map-swap-cauchy-approximation-Metric-Space)
  is-cauchy-map-swap-cauchy-approximation-Metric-Space ε δ η =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      ( A)
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A)
        ( U)
        ( η))
      ( ε)
      ( δ)

  swap-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
  swap-cauchy-approximation-Metric-Space =
    ( map-swap-cauchy-approximation-Metric-Space ,
      is-cauchy-map-swap-cauchy-approximation-Metric-Space)
```

### Swapping the arguments of a Cauchy approximation of Cauchy approximations is an involution

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-involution-swap-cauchy-approximation-Metric-Space :
    is-involution
      ( swap-cauchy-approximation-Metric-Space A)
  is-involution-swap-cauchy-approximation-Metric-Space U =
    eq-htpy-cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( λ ε →
        eq-htpy-cauchy-approximation-Metric-Space
          ( A)
          ( λ δ → refl))

  is-equiv-swap-cauchy-approximation-Metric-Space :
    is-equiv (swap-cauchy-approximation-Metric-Space A)
  is-equiv-swap-cauchy-approximation-Metric-Space =
    is-equiv-is-involution
      is-involution-swap-cauchy-approximation-Metric-Space

  equiv-swap-cauchy-approximation-Metric-Space :
    ( cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)) ≃
    ( cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A))
  equiv-swap-cauchy-approximation-Metric-Space =
    ( swap-cauchy-approximation-Metric-Space A ,
      is-equiv-swap-cauchy-approximation-Metric-Space)
```

### Swapping the arguments of a Cauchy approximation of Cauchy approximations is a short map

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-short-map-swap-cauchy-approximation-Metric-Space :
    is-short-map-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
      ( swap-cauchy-approximation-Metric-Space A)
  is-short-map-swap-cauchy-approximation-Metric-Space ε U V Nuv δ η =
    Nuv η δ
```

### Swapping the arguments of a Cauchy approximation of Cauchy approximations is an isometry

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-isometry-swap-cauchy-approximation-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
      ( swap-cauchy-approximation-Metric-Space A)
  is-isometry-swap-cauchy-approximation-Metric-Space ε U V =
    ( is-short-map-swap-cauchy-approximation-Metric-Space A ε U V ,
      is-short-map-swap-cauchy-approximation-Metric-Space
        ( A)
        ( ε)
        ( swap-cauchy-approximation-Metric-Space A U)
        ( swap-cauchy-approximation-Metric-Space A V))
```

### Swapping the arguments of a Cauchy approximation of Cauchy approximations is an isometric equivalence

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  isometric-equiv-swap-cauchy-approximation-Metric-Space :
    isometric-equiv-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
      ( metric-space-of-cauchy-approximations-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A))
  isometric-equiv-swap-cauchy-approximation-Metric-Space =
    ( equiv-swap-cauchy-approximation-Metric-Space A ,
      is-isometry-swap-cauchy-approximation-Metric-Space A)
```
