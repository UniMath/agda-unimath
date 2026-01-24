# Metric quotients of metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-quotients-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of the underlying [pseudometric space](metric-spaces.pseudometric-spaces.md) of
a [metric space](metric-spaces.metric-spaces.md) `M` is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to `M`.

## Definitions

### Metric quotients of metric spaces

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  metric-quotient-Metric-Space : Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-quotient-Metric-Space =
    metric-quotient-Pseudometric-Space
      (pseudometric-Metric-Space M)
```

### The unit map from a metric space into its metric quotient

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  unit-map-metric-quotient-Metric-Space :
    map-Metric-Space M
      (metric-quotient-Metric-Space M)
  unit-map-metric-quotient-Metric-Space =
    unit-map-metric-quotient-Pseudometric-Space
      (pseudometric-Metric-Space M)

  compute-unit-map-metric-quotient-Metric-Space :
    ( X :
      type-metric-quotient-Pseudometric-Space
        ( pseudometric-Metric-Space M)) →
    { x : type-Metric-Space M} →
    is-in-class-metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( X)
      ( x) →
    unit-map-metric-quotient-Metric-Space x ＝ X
  compute-unit-map-metric-quotient-Metric-Space =
    compute-unit-map-metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

## Theorem

### The unit map from a metric space into its metric quotient is an equivalence

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where abstract

  is-contr-map-unit-map-metric-quotient-Metric-Space :
    is-contr-map (unit-map-metric-quotient-Metric-Space M)
  is-contr-map-unit-map-metric-quotient-Metric-Space X =
    let
      open
        do-syntax-trunc-Prop
          ( is-contr-Prop
            ( fiber (unit-map-metric-quotient-Metric-Space M) X))
      in do
        ( x , x∈X) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Metric-Space M)
            ( X)

        let
          center-fiber : fiber (unit-map-metric-quotient-Metric-Space M) X
          center-fiber =
            ( x , compute-unit-map-metric-quotient-Metric-Space M X x∈X)

          contraction-fiber :
            ( y : fiber (unit-map-metric-quotient-Metric-Space M) X) →
            center-fiber ＝ y
          contraction-fiber (y , [y]=X) =
            eq-type-subtype
              ( λ z →
                eq-prop-Metric-Space
                  ( metric-quotient-Metric-Space M)
                  ( unit-map-metric-quotient-Metric-Space M z)
                  ( X))
              ( eq-sim-Metric-Space M x y
                ( apply-effectiveness-quotient-map
                  ( equivalence-relation-sim-Metric-Space M)
                  ( compute-unit-map-metric-quotient-Metric-Space M X x∈X ∙
                    inv [y]=X)))

        ( center-fiber , contraction-fiber)

  is-equiv-unit-map-metric-quotient-Metric-Space :
    is-equiv (unit-map-metric-quotient-Metric-Space M)
  is-equiv-unit-map-metric-quotient-Metric-Space =
    is-equiv-is-contr-map
      is-contr-map-unit-map-metric-quotient-Metric-Space
```

## Applications

### The isometric equivalence between a metric space and its metric quotient

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometric-equiv-unit-metric-quotient-Metric-Space' :
    isometric-equiv-Metric-Space'
      ( M)
      ( metric-quotient-Pseudometric-Space
        ( pseudometric-Metric-Space M))
  isometric-equiv-metric-quotient-Metric-Space' =
    ( unit-map-metric-quotient-Metric-Space M ,
      is-equiv-unit-map-metric-quotient-Metric-Space M ,
      is-isometry-unit-map-metric-quotient-Pseudometric-Space
        ( pseudometric-Metric-Space M))
```

### The construction of the quotient metric space of a pseudometric space is idempotent

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-idempotent-metric-quotient-Pseudometric-Space :
    metric-quotient-Pseudometric-Space
      ( pseudometric-Metric-Space
        ( metric-quotient-Pseudometric-Space M)) ＝
    metric-quotient-Pseudometric-Space M
  is-idempotent-metric-quotient-Pseudometric-Space =
    inv
      ( eq-isometric-equiv-Metric-Space'
        ( metric-quotient-Pseudometric-Space M)
        ( metric-quotient-Pseudometric-Space
          ( pseudometric-Metric-Space
            ( metric-quotient-Pseudometric-Space M)))
        ( isometric-equiv-metric-quotient-Metric-Space'
          ( metric-quotient-Pseudometric-Space M)))
```
