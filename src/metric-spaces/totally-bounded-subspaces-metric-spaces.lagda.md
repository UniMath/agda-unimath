# Totally bounded subspaces of metric spaces

```agda
module metric-spaces.totally-bounded-subspaces-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-products-subtypes
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.subtypes-of-subtypes
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

A
{{#concept "totally bounded" disambiguation="subspace of a metric space" WDID=Q1362228 WD="totally bounded space" Agda=totally-bounded-subspace-Metric-Space}}
[subspace](metric-spaces.subspaces-metric-spaces.md) of a
[metric space](metric-spaces.metric-spaces.md) is a subspace that is
[totally bounded](metric-spaces.totally-bounded-metric-spaces.md).

## Definition

```agda
is-totally-bounded-subset-Metric-Space :
  {l1 l2 l3 : Level} (l4 : Level) (X : Metric-Space l1 l2) →
  subset-Metric-Space l3 X → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
is-totally-bounded-subset-Metric-Space l4 X S =
  is-totally-bounded-Metric-Space l4 (subspace-Metric-Space X S)

totally-bounded-subspace-Metric-Space :
  {l1 l2 : Level} (l3 l4 : Level) → Metric-Space l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
totally-bounded-subspace-Metric-Space l3 l4 X =
  Σ ( subset-Metric-Space l3 X)
    ( is-totally-bounded-subset-Metric-Space l4 X)

module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (S : totally-bounded-subspace-Metric-Space l3 l4 X)
  where

  subset-totally-bounded-subspace-Metric-Space : subset-Metric-Space l3 X
  subset-totally-bounded-subspace-Metric-Space = pr1 S

  type-totally-bounded-subspace-Metric-Space : UU (l1 ⊔ l3)
  type-totally-bounded-subspace-Metric-Space =
    type-subtype subset-totally-bounded-subspace-Metric-Space

  inclusion-totally-bounded-subspace-Metric-Space :
    type-totally-bounded-subspace-Metric-Space → type-Metric-Space X
  inclusion-totally-bounded-subspace-Metric-Space =
    inclusion-subtype subset-totally-bounded-subspace-Metric-Space

  subspace-totally-bounded-subspace-Metric-Space : Metric-Space (l1 ⊔ l3) l2
  subspace-totally-bounded-subspace-Metric-Space =
    subspace-Metric-Space X subset-totally-bounded-subspace-Metric-Space

  is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space :
    is-totally-bounded-Metric-Space
      ( l4)
      ( subspace-totally-bounded-subspace-Metric-Space)
  is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space =
    pr2 S

  totally-bounded-space-totally-bounded-subspace-Metric-Space :
    Totally-Bounded-Metric-Space (l1 ⊔ l3) l2 l4
  totally-bounded-space-totally-bounded-subspace-Metric-Space =
    ( subspace-totally-bounded-subspace-Metric-Space ,
      is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space)
```

## Properties

### The image of a totally bounded space under a uniformly continuous map

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X@(msX , tbX) : Totally-Bounded-Metric-Space l1 l2 l3)
  (Y : Metric-Space l4 l5)
  (f@(map-f , uc-f) :
    uniformly-continuous-map-Metric-Space
      ( metric-space-Totally-Bounded-Metric-Space X)
      ( Y))
  where

  subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space :
    subset-Metric-Space (l1 ⊔ l4) Y
  subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space =
    subtype-im map-f

  abstract
    is-totally-bounded-subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space :
      is-totally-bounded-subset-Metric-Space
        ( l1 ⊔ l3 ⊔ l4)
        ( Y)
        ( subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space)
    is-totally-bounded-subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space =
      is-totally-bounded-im-uniformly-continuous-map-is-totally-bounded-Metric-Space
        ( msX)
        ( Y)
        ( tbX)
        ( f)

  im-uniformly-continuous-map-Totally-Bounded-Metric-Space :
    totally-bounded-subspace-Metric-Space (l1 ⊔ l4) (l1 ⊔ l3 ⊔ l4) Y
  im-uniformly-continuous-map-Totally-Bounded-Metric-Space =
    ( subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space ,
      is-totally-bounded-subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space)
```

### The image of a totally bounded subspace under a uniformly continuous map

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : uniformly-continuous-map-Metric-Space X Y)
  (S : totally-bounded-subspace-Metric-Space l5 l6 X)
  where

  subset-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space :
    subset-Metric-Space (l1 ⊔ l3 ⊔ l5) Y
  subset-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space =
    im-subtype
      ( map-uniformly-continuous-map-Metric-Space X Y f)
      ( subset-totally-bounded-subspace-Metric-Space X S)

  abstract
    is-totally-bounded-subspace-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space :
      is-totally-bounded-subset-Metric-Space
        ( l1 ⊔ l3 ⊔ l5 ⊔ l6)
        ( Y)
        ( subset-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space)
    is-totally-bounded-subspace-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space =
      is-totally-bounded-subset-im-uniformly-continuous-map-Totally-Bounded-Metric-Space
        ( totally-bounded-space-totally-bounded-subspace-Metric-Space X S)
        ( Y)
        ( comp-uniformly-continuous-map-Metric-Space
          ( subspace-totally-bounded-subspace-Metric-Space X S)
          ( X)
          ( Y)
          ( f)
          ( uniformly-continuous-inclusion-subspace-Metric-Space
            ( X)
            ( subset-totally-bounded-subspace-Metric-Space X S)))

  im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space :
    totally-bounded-subspace-Metric-Space (l1 ⊔ l3 ⊔ l5) (l1 ⊔ l3 ⊔ l5 ⊔ l6) Y
  im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space =
    ( subset-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space ,
      is-totally-bounded-subspace-im-uniformly-continuous-map-totally-bounded-subspace-Metric-Space)
```

### Totally bounded subspaces of metric spaces are closed under Cartesian products

```agda
product-totally-bounded-subspace-Metric-Space :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} →
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  (S : totally-bounded-subspace-Metric-Space l5 l6 X) →
  (T : totally-bounded-subspace-Metric-Space l7 l8 Y) →
  totally-bounded-subspace-Metric-Space
    ( l5 ⊔ l7)
    ( l1 ⊔ l3 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
    ( product-Metric-Space X Y)
product-totally-bounded-subspace-Metric-Space X Y (S , tbS) (T , tbT) =
  ( product-subtype S T ,
    preserves-is-totally-bounded-isometric-equiv-Metric-Space
      ( product-Metric-Space
        ( subspace-Metric-Space X S)
        ( subspace-Metric-Space Y T))
      ( subspace-Metric-Space (product-Metric-Space X Y) (product-subtype S T))
      ( is-totally-bounded-product-Totally-Bounded-Metric-Space
        ( subspace-Metric-Space X S , tbS)
        ( subspace-Metric-Space Y T , tbT))
      ( inv-equiv (equiv-product-subtype S T) , (λ _ _ _ → id-iff)))
```

### If `T` is a subspace of `S` is a subspace of `X` and `T` is totally bounded in `S`, `T` is totally bounded in `X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : Metric-Space l1 l2)
  (S : subset-Metric-Space l3 X)
  (T : subset-Metric-Space l4 (subspace-Metric-Space X S))
  where abstract

  is-totally-bounded-subspace-of-subspace-Metric-Space :
    is-totally-bounded-subset-Metric-Space l5 (subspace-Metric-Space X S) T →
    is-totally-bounded-subset-Metric-Space
      ( l1 ⊔ l3 ⊔ l4 ⊔ l5)
      ( X)
      ( subtype-subtype-of-subtype S T)
  is-totally-bounded-subspace-of-subspace-Metric-Space tbT⊆S =
    preserves-is-totally-bounded-isometric-equiv-Metric-Space
      ( subspace-Metric-Space (subspace-Metric-Space X S) T)
      ( subspace-Metric-Space X (subtype-subtype-of-subtype S T))
      ( tbT⊆S)
      ( isometric-equiv-subspace-of-subspace-Metric-Space X S T)
```

### Total boundedness is preserved by similarity of subtypes

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : Metric-Space l1 l2)
  (S : subset-Metric-Space l3 X)
  (T : subset-Metric-Space l4 X)
  where abstract

  preserves-is-totally-bounded-sim-subset-Metric-Space :
    sim-subtype S T →
    is-totally-bounded-subset-Metric-Space l5 X S →
    is-totally-bounded-subset-Metric-Space (l1 ⊔ l3 ⊔ l4 ⊔ l5) X T
  preserves-is-totally-bounded-sim-subset-Metric-Space S~T tb-S =
    preserves-is-totally-bounded-isometric-equiv-Metric-Space
      ( subspace-Metric-Space X S)
      ( subspace-Metric-Space X T)
      ( tb-S)
      ( isometric-equiv-sim-subspace-Metric-Space X S T S~T)
```
