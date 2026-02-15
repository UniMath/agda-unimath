# The unit map of metric quotients of pseudometric spaces

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
{{#concept "unit map" Disambiguation="of metric quotients" Agda=map-unit-metric-quotient-Pseudometric-Space}}
of the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
construction is the [quotient map](foundation.set-quotients.md)

```text
  q : P → [P].
```

It is an [isometry](metric-spaces.isometries-pseudometric-spaces.md) from the
pseudometric space `P` to the underlying pseudometric space of the
[metric space](metric-spaces.metric-spaces.md) `[P]`.

## Definitions

### The unit map from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where

  map-unit-metric-quotient-Pseudometric-Space :
    map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
  map-unit-metric-quotient-Pseudometric-Space =
    quotient-map (equivalence-relation-sim-Pseudometric-Space P)

  is-in-class-map-unit-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space P) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( P)
      ( map-unit-metric-quotient-Pseudometric-Space x)
      ( x)
  is-in-class-map-unit-metric-quotient-Pseudometric-Space =
    is-in-equivalence-class-quotient-map-set-quotient
      (equivalence-relation-sim-Pseudometric-Space P)

  map-subtype-map-unit-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space P) →
    type-subtype-metric-quotient-Pseudometric-Space P
      (map-unit-metric-quotient-Pseudometric-Space x)
  map-subtype-map-unit-metric-quotient-Pseudometric-Space =
    inhabitant-equivalence-class-quotient-map-set-quotient
      (equivalence-relation-sim-Pseudometric-Space P)

  compute-map-unit-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space P) →
    {x : type-Pseudometric-Space P} →
    is-in-class-metric-quotient-Pseudometric-Space P X x →
    map-unit-metric-quotient-Pseudometric-Space x ＝ X
  compute-map-unit-metric-quotient-Pseudometric-Space X {x} x∈X =
    eq-set-quotient-equivalence-class-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space P)
      ( X)
      ( x∈X)
```

## Properties

### The unit map is an isometry

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where abstract

  preserves-neighborhoods-map-unit-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space P) →
    neighborhood-Pseudometric-Space P d x y →
    neighborhood-metric-quotient-Pseudometric-Space
      ( P)
      ( d)
      ( map-unit-metric-quotient-Pseudometric-Space P x)
      ( map-unit-metric-quotient-Pseudometric-Space P y)
  preserves-neighborhoods-map-unit-metric-quotient-Pseudometric-Space
    d x y d⟨x,y⟩ (x' , x≈x') (y' , y≈y') =
    let
      x~x' =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space P)
          ( x)
          ( x')
          ( x≈x')

      y~y' =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space P)
          ( y)
          ( y')
          ( y≈y')

    in
      preserves-neighborhoods-right-sim-Pseudometric-Space P y~y' d x'
        ( preserves-neighborhoods-left-sim-Pseudometric-Space
          ( P)
          ( x~x')
          ( d)
          ( y)
          ( d⟨x,y⟩))

  reflects-neighborhoods-map-unit-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space P) →
    neighborhood-metric-quotient-Pseudometric-Space
      ( P)
      ( d)
      ( map-unit-metric-quotient-Pseudometric-Space P x)
      ( map-unit-metric-quotient-Pseudometric-Space P y) →
    neighborhood-Pseudometric-Space P d x y
  reflects-neighborhoods-map-unit-metric-quotient-Pseudometric-Space
    d x y Nxy =
      Nxy
        ( map-subtype-map-unit-metric-quotient-Pseudometric-Space P x)
        ( map-subtype-map-unit-metric-quotient-Pseudometric-Space P y)

  is-isometry-map-unit-metric-quotient-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      ( map-unit-metric-quotient-Pseudometric-Space P)
  pr1 (is-isometry-map-unit-metric-quotient-Pseudometric-Space d x y) =
    preserves-neighborhoods-map-unit-metric-quotient-Pseudometric-Space d x y
  pr2 (is-isometry-map-unit-metric-quotient-Pseudometric-Space d x y) =
    reflects-neighborhoods-map-unit-metric-quotient-Pseudometric-Space d x y
```

### The unit isometry from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-unit-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
  isometry-unit-metric-quotient-Pseudometric-Space =
    ( map-unit-metric-quotient-Pseudometric-Space P ,
      is-isometry-map-unit-metric-quotient-Pseudometric-Space P)
```

### The unit short map from a pseudometric space to its quotient metric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  short-map-unit-metric-quotient-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
  short-map-unit-metric-quotient-Pseudometric-Space =
    short-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      (isometry-unit-metric-quotient-Pseudometric-Space P)
```

## See also

- The
  [universal property of metric quotients and short maps](metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces.md);
- the
  [universal property of metric quotients and isometries](metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces.md).
