# Unit map of metric quotients of pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-quotients
open import foundation.universe-levels

open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "unit map" Disambiguation="of metric quotients" Agda=unit-map-metric-quotient-Pseudometric-Space}}
of the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
construction is the [quotient map](foundation.set-quotients.md)

```text
  η : P → [P].
```

It is an [isometry](metric-spaces.isometries-pseudometric-spaces.md) from the
pseudometric space `P` to the underlying pseudometric space of the
[metric space](metric-spaces.metric-spaces.md) `[P]`.

## Definitions

### Homomorphisms from a pseudometric space to its metric quotient

#### Maps

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  map-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2)
  map-metric-quotient-Pseudometric-Space =
    map-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)
```

#### Short maps

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  short-map-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2)
  short-map-metric-quotient-Pseudometric-Space =
    short-map-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)

  map-short-map-metric-quotient-Pseudometric-Space :
    short-map-metric-quotient-Pseudometric-Space →
    map-metric-quotient-Pseudometric-Space M
  map-short-map-metric-quotient-Pseudometric-Space =
    map-short-map-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)
```

#### Isometries

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  isometry-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2)
  isometry-metric-quotient-Pseudometric-Space =
    isometry-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)

  short-map-isometry-metric-quotient-Pseudometric-Space :
    isometry-metric-quotient-Pseudometric-Space →
    short-map-metric-quotient-Pseudometric-Space M
  short-map-isometry-metric-quotient-Pseudometric-Space =
    short-map-isometry-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)

  map-isometry-metric-quotient-Pseudometric-Space :
    isometry-metric-quotient-Pseudometric-Space →
    map-metric-quotient-Pseudometric-Space M
  map-isometry-metric-quotient-Pseudometric-Space =
    map-isometry-Pseudometric-Space M
      (pseudometric-metric-quotient-Pseudometric-Space M)
```

### The unit map from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where

  unit-map-metric-quotient-Pseudometric-Space :
    map-metric-quotient-Pseudometric-Space M
  unit-map-metric-quotient-Pseudometric-Space =
    quotient-map (equivalence-relation-sim-Pseudometric-Space M)

  is-in-class-unit-map-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( M)
      ( unit-map-metric-quotient-Pseudometric-Space x)
      ( x)
  is-in-class-unit-map-metric-quotient-Pseudometric-Space =
    is-in-equivalence-class-quotient-map-set-quotient
      (equivalence-relation-sim-Pseudometric-Space M)

  map-subtype-unit-map-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space M) →
    type-subtype-metric-quotient-Pseudometric-Space M
      (unit-map-metric-quotient-Pseudometric-Space x)
  map-subtype-unit-map-metric-quotient-Pseudometric-Space =
    inhabitant-equivalence-class-quotient-map-set-quotient
      (equivalence-relation-sim-Pseudometric-Space M)

  compute-unit-map-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space M) →
    {x : type-Pseudometric-Space M} →
    is-in-class-metric-quotient-Pseudometric-Space M X x →
    unit-map-metric-quotient-Pseudometric-Space x ＝ X
  compute-unit-map-metric-quotient-Pseudometric-Space X {x} x∈X =
    eq-set-quotient-equivalence-class-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space M)
      ( X)
      ( x∈X)
```

## Properties

### The unit map from a pseudometric space its quotient metric space is an isometry

```agda
module _
  {l1 l2 : Level}
  (M : Pseudometric-Space l1 l2)
  where abstract

  preserves-neighborhoods-unit-map-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
    neighborhood-Pseudometric-Space M d x y →
    neighborhood-metric-quotient-Pseudometric-Space
      ( M)
      ( d)
      ( unit-map-metric-quotient-Pseudometric-Space M x)
      ( unit-map-metric-quotient-Pseudometric-Space M y)
  preserves-neighborhoods-unit-map-metric-quotient-Pseudometric-Space
    d x y d⟨x,y⟩ (x' , x≈x') (y' , y≈y') =
    let
      x~x' =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space M)
          ( x)
          ( x')
          ( x≈x')

      y~y' =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space M)
          ( y)
          ( y')
          ( y≈y')

    in
      preserves-neighborhoods-right-sim-Pseudometric-Space M y~y' d x'
        ( preserves-neighborhoods-left-sim-Pseudometric-Space
          ( M)
          ( x~x')
          ( d)
          ( y)
          ( d⟨x,y⟩))

  reflects-neighborhoods-unit-map-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
    neighborhood-metric-quotient-Pseudometric-Space
      ( M)
      ( d)
      ( unit-map-metric-quotient-Pseudometric-Space M x)
      ( unit-map-metric-quotient-Pseudometric-Space M y) →
    neighborhood-Pseudometric-Space M d x y
  reflects-neighborhoods-unit-map-metric-quotient-Pseudometric-Space
    d x y Nxy =
      Nxy
        ( map-subtype-unit-map-metric-quotient-Pseudometric-Space M x)
        ( map-subtype-unit-map-metric-quotient-Pseudometric-Space M y)

  is-isometry-unit-map-metric-quotient-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
      ( unit-map-metric-quotient-Pseudometric-Space M)
  pr1 (is-isometry-unit-map-metric-quotient-Pseudometric-Space d x y) =
    preserves-neighborhoods-unit-map-metric-quotient-Pseudometric-Space d x y
  pr2 (is-isometry-unit-map-metric-quotient-Pseudometric-Space d x y) =
    reflects-neighborhoods-unit-map-metric-quotient-Pseudometric-Space d x y
```

### The unit isometry from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  unit-isometry-metric-quotient-Pseudometric-Space :
    isometry-metric-quotient-Pseudometric-Space M
  unit-isometry-metric-quotient-Pseudometric-Space =
    ( unit-map-metric-quotient-Pseudometric-Space M ,
      is-isometry-unit-map-metric-quotient-Pseudometric-Space M)
```

### The unit short map from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  unit-short-map-metric-quotient-Pseudometric-Space :
    short-map-metric-quotient-Pseudometric-Space M
  unit-short-map-metric-quotient-Pseudometric-Space =
    short-map-isometry-metric-quotient-Pseudometric-Space M
      (unit-isometry-metric-quotient-Pseudometric-Space M)
```

## See also

- The
  [universal property of metric quotients and short maps](metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces.md);
- the
  [universal property of metric quotients and isometries](metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces.md).

## External links

- [Metric identification](https://en.wikipedia.org/wiki/Pseudometric_space#Metric_identification)
  on pseudometric spaces at Wikipedia
