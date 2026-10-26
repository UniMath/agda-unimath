# Limits of Cauchy filters on pseudometric spaces

```agda
module metric-spaces.limits-of-cauchy-filters-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A point `x` of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M`
is called a
{{#concept "limit" Disambiguation="of a Cauchy filter in a pseudometric space" Agda=is-limit-cauchy-filter-Pseudometric-Space}}
of a [Cauchy filter](metric-spaces.cauchy-filters-pseudometric-spaces.md) `U` if
`x ∈ U ε` for all `ε : ℚ⁺`, i.e., `x` is in the intersection of all the
neighborhood subtypes of the Cauchy filter.

All limits are
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md).

## Definitions

### The property of being a limit of a Cauchy filter in a pseudometric space

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : cauchy-filter-Pseudometric-Space l M)
  (x : type-Pseudometric-Space M)
  where

  is-limit-prop-cauchy-filter-Pseudometric-Space : Prop l
  is-limit-prop-cauchy-filter-Pseudometric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d → neighborhood-subtype-cauchy-filter-Pseudometric-Space M U d x)

  is-limit-cauchy-filter-Pseudometric-Space : UU l
  is-limit-cauchy-filter-Pseudometric-Space =
    type-Prop is-limit-prop-cauchy-filter-Pseudometric-Space

  is-prop-is-limit-cauchy-filter-Pseudometric-Space :
    is-prop is-limit-cauchy-filter-Pseudometric-Space
  is-prop-is-limit-cauchy-filter-Pseudometric-Space =
    is-prop-type-Prop is-limit-prop-cauchy-filter-Pseudometric-Space
```

## Properties

### All limits are similar

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : cauchy-filter-Pseudometric-Space l M)
  where

  all-sim-is-limit-cauchy-filter-Pseudometric-Space :
    (x y : type-Pseudometric-Space M) →
    is-limit-cauchy-filter-Pseudometric-Space M U x →
    is-limit-cauchy-filter-Pseudometric-Space M U y →
    sim-Pseudometric-Space M x y
  all-sim-is-limit-cauchy-filter-Pseudometric-Space x y Lx Ly d =
    elim-exists
      ( neighborhood-prop-Pseudometric-Space M d x y)
      ( λ ε ε+ε<d →
        monotonic-neighborhood-Pseudometric-Space
          ( M)
          ( x)
          ( y)
          ( ε +ℚ⁺ ε)
          ( d)
          ( ε+ε<d)
          ( is-bounded-cauchy-filter-Pseudometric-Space
            ( M)
            ( U)
            ( ε)
            ( ε)
            ( x)
            ( y)
            ( Lx ε)
            ( Ly ε)))
      ( double-le-ℚ⁺ d)
```

### Points are limits of their image by the unit map of Cauchy filters in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-limit-map-unit-cauchy-filter-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    is-limit-cauchy-filter-Pseudometric-Space
      ( M)
      ( map-unit-cauchy-filter-Pseudometric-Space M x)
      ( x)
  is-limit-map-unit-cauchy-filter-Pseudometric-Space x ε =
    is-in-filter-map-unit-cauchy-filter-Pseudometric-Space M ε x
```
