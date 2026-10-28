# Limits of Cauchy filters on metric spaces

```agda
module metric-spaces.limits-of-cauchy-filters-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

In a [metric space](metric-spaces.metric-spaces.md), all
[limits](metric-spaces.limits-of-cauchy-filters-pseudometric-spaces.md) of
[Cauchy filters](metric-spaces.cauchy-filters-metric-spaces.md) are
[equal](foundation.identity-types.md).

Therefore, the existence of a
{{#concept "limit" Disambiguation="of a Cauchy filter in a metric space Agda=limit-cauchy-filter-Metric-Space}}
of a Cauchy filter is a [proposition](foundation.propositions.md).

## Definitions

### The property of being a limit of a Cauchy filter in a metric space

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  is-limit-prop-cauchy-filter-Metric-Space : (x : type-Metric-Space M) → Prop l
  is-limit-prop-cauchy-filter-Metric-Space x =
    is-limit-prop-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)
      ( x)

  is-limit-cauchy-filter-Metric-Space : (x : type-Metric-Space M) → UU l
  is-limit-cauchy-filter-Metric-Space x =
    type-Prop (is-limit-prop-cauchy-filter-Metric-Space x)

  is-prop-is-limit-cauchy-filter-Metric-Space :
    (x : type-Metric-Space M) →
    is-prop (is-limit-cauchy-filter-Metric-Space x)
  is-prop-is-limit-cauchy-filter-Metric-Space x =
    is-prop-type-Prop (is-limit-prop-cauchy-filter-Metric-Space x)
```

### The subtype of limits of a Cauchy filter in a metric space

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  limit-cauchy-filter-Metric-Space : UU (l1 ⊔ l)
  limit-cauchy-filter-Metric-Space =
    type-subtype (is-limit-prop-cauchy-filter-Metric-Space M U)
```

## Properties

### All limits are equal

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  all-eq-is-limit-cauchy-filter-Metric-Space :
    (x y : type-Metric-Space M) →
    is-limit-cauchy-filter-Metric-Space M U x →
    is-limit-cauchy-filter-Metric-Space M U y →
    x ＝ y
  all-eq-is-limit-cauchy-filter-Metric-Space x y Lx Ly =
    eq-sim-Metric-Space
      ( M)
      ( x)
      ( y)
      ( all-sim-is-limit-cauchy-filter-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( U)
        ( x)
        ( y)
        ( Lx)
        ( Ly))

  all-eq-limit-cauchy-filter-Metric-Space :
    (x y : limit-cauchy-filter-Metric-Space M U) → x ＝ y
  all-eq-limit-cauchy-filter-Metric-Space (x , Lx) (y , Ly) =
    eq-type-subtype
      ( is-limit-prop-cauchy-filter-Metric-Space M U)
      ( all-eq-is-limit-cauchy-filter-Metric-Space x y Lx Ly)
```

### Having a limit is a property

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  is-prop-limit-cauchy-filter-Metric-Space :
    is-prop (limit-cauchy-filter-Metric-Space M U)
  is-prop-limit-cauchy-filter-Metric-Space =
    is-prop-all-elements-equal (all-eq-limit-cauchy-filter-Metric-Space M U)

  limit-prop-cauchy-filter-Metric-Space : Prop (l1 ⊔ l)
  limit-prop-cauchy-filter-Metric-Space =
    ( limit-cauchy-filter-Metric-Space M U ,
      is-prop-limit-cauchy-filter-Metric-Space)
```

### Points are limits of their image by the unit map of Cauchy filters in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-limit-map-unit-cauchy-filter-Metric-Space :
    (x : type-Metric-Space M) →
    is-limit-cauchy-filter-Metric-Space
      ( M)
      ( map-unit-cauchy-filter-Metric-Space M x)
      ( x)
  is-limit-map-unit-cauchy-filter-Metric-Space =
    is-limit-map-unit-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```
