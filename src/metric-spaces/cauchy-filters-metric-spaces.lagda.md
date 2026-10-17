# Cauchy filters on metric spaces

```agda
module metric-spaces.cauchy-filters-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy filter" Disambiguation="on a metric space" Agda=cauchy-filter-Metric-Space}}
on a [metric space](metric-spaces.metric-spaces.md) `M` is a
[Cauchy filter](metric-spaces.cauchy-filters-pseudometric-spaces.md) on the
underlying [pseudometric space](metric-spaces.pseudometric-spaces.md).

The type of Cauchy filters is equipped with a unit map `η : M → F(M)`; it can be
equipped with a metric structure turning `F(M)` into a
[complete metric space](metric-spaces.complete-metric-spaces.md) where `η` is an
isometry.

## Definitions

### The type of Cauchy filters on a metric space

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  cauchy-filter-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l)
  cauchy-filter-Metric-Space =
    cauchy-filter-Pseudometric-Space l (pseudometric-Metric-Space M)
```

### Components of Cauchy filters

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  subtype-cauchy-filter-Metric-Space :
    Rational-Neighborhood-Subtype l (type-Metric-Space M)
  subtype-cauchy-filter-Metric-Space =
    subtype-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-in-cauchy-filter-Metric-Space : ℚ⁺ → type-Metric-Space M → UU l
  is-in-cauchy-filter-Metric-Space =
    is-in-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-cauchy-filter-subtype-cauchy-filter-Metric-Space :
    is-cauchy-filter-Pseudometric-Space
      ( l)
      ( pseudometric-Metric-Space M)
      ( subtype-cauchy-filter-Metric-Space)
  is-cauchy-filter-subtype-cauchy-filter-Metric-Space =
    is-cauchy-filter-subtype-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-proper-cauchy-filter-Metric-Space :
    is-proper-Rational-Neighborhood-Subtype
      subtype-cauchy-filter-Metric-Space
  is-proper-cauchy-filter-Metric-Space =
    is-proper-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-saturated-cauchy-filter-Metric-Space :
    is-saturated-Rational-Neighborhood-Subtype
      subtype-cauchy-filter-Metric-Space
  is-saturated-cauchy-filter-Metric-Space =
    is-saturated-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-local-cauchy-filter-Metric-Space :
    is-local-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( subtype-cauchy-filter-Metric-Space)
  is-local-cauchy-filter-Metric-Space =
    is-local-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-bounded-cauchy-filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-cauchy-filter-Metric-Space ε x →
    is-in-cauchy-filter-Metric-Space δ y →
    neighborhood-Metric-Space M (ε +ℚ⁺ δ) x y
  is-bounded-cauchy-filter-Metric-Space =
    is-bounded-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  is-enclosing-cauchy-filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-cauchy-filter-Metric-Space ε x →
    neighborhood-Metric-Space M δ x y →
    is-in-cauchy-filter-Metric-Space (ε +ℚ⁺ δ) y
  is-enclosing-cauchy-filter-Metric-Space =
    is-enclosing-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)
```

### The unit map of Cauchy filters

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  map-unit-cauchy-filter-Metric-Space :
    type-Metric-Space M → cauchy-filter-Metric-Space l2 M
  map-unit-cauchy-filter-Metric-Space =
    map-unit-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

## Properties

### Cauchy filters are monotonic

For any Cauchy filter `U` and `ε δ : ℚ⁺` with `ε < δ`, `Uε ⊆ Uδ`.

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (U : cauchy-filter-Metric-Space l M)
  where

  is-monotonic-cauchy-filter-Metric-Space :
    ( x : type-Metric-Space M) →
    ( ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-Metric-Space M U ε x →
    is-in-cauchy-filter-Metric-Space M U δ x
  is-monotonic-cauchy-filter-Metric-Space =
    is-monotonic-cauchy-filter-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)
```

### Any point is in the filter of its image by the unit map

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-in-filter-map-unit-cauchy-filter-Metric-Space :
    ( ε : ℚ⁺) →
    ( x : type-Metric-Space M) →
    is-in-cauchy-filter-Metric-Space
      ( M)
      ( map-unit-cauchy-filter-Metric-Space M x)
      ( ε)
      ( x)
  is-in-filter-map-unit-cauchy-filter-Metric-Space ε x =
    refl-neighborhood-Metric-Space M ε x
```

## References

This definition essentially corresponds to "Cauchy filters of formal balls" as
described in {{#cite Vickers2005localic}}, with **closed** (i.e. saturated)
formal balls.

{{#bibliography}}
