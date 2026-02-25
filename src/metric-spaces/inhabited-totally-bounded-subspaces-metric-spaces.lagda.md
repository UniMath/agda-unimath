# Inhabited, totally bounded subspaces of metric spaces

```agda
module metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-products-subtypes
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import logic.propositionally-decidable-types

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.totally-bounded-subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

An
{{#concept "inhabited, totally bounded subspace" Disambiguation="of a metric space" Agda=inhabited-totally-bounded-subspace-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `X` is a
[subspace](metric-spaces.subspaces-metric-spaces.md) `S ⊆ X` that is
[totally bounded](metric-spaces.totally-bounded-subspaces-metric-spaces.md) and
[inhabited](foundation.inhabited-subtypes.md).

## Definition

```agda
inhabited-totally-bounded-subspace-Metric-Space :
  {l1 l2 : Level} (l3 l4 : Level) → Metric-Space l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
inhabited-totally-bounded-subspace-Metric-Space l3 l4 X =
  Σ ( totally-bounded-subspace-Metric-Space l3 l4 X)
    ( λ S →
      is-inhabited-subtype (subset-totally-bounded-subspace-Metric-Space X S))

module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (S : inhabited-totally-bounded-subspace-Metric-Space l3 l4 X)
  where

  totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space :
    totally-bounded-subspace-Metric-Space l3 l4 X
  totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space =
    pr1 S

  subset-inhabited-totally-bounded-subspace-Metric-Space :
    subset-Metric-Space l3 X
  subset-inhabited-totally-bounded-subspace-Metric-Space =
    subset-totally-bounded-subspace-Metric-Space
      ( X)
      ( totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space)

  subspace-inhabited-totally-bounded-subspace-Metric-Space :
    Metric-Space (l1 ⊔ l3) l2
  subspace-inhabited-totally-bounded-subspace-Metric-Space =
    subspace-totally-bounded-subspace-Metric-Space
      ( X)
      ( totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space)

  is-totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space :
    is-totally-bounded-Metric-Space
      ( l4)
      ( subspace-inhabited-totally-bounded-subspace-Metric-Space)
  is-totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space =
    is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space
      ( X)
      ( totally-bounded-subspace-inhabited-totally-bounded-subspace-Metric-Space)

  is-inhabited-inhabited-totally-bounded-subspace-Metric-Space :
    is-inhabited-subtype subset-inhabited-totally-bounded-subspace-Metric-Space
  is-inhabited-inhabited-totally-bounded-subspace-Metric-Space = pr2 S
```

## Properties

### The image of an inhabited totally bounded metric space under a uniformly continuous function is an inhabited totally bounded subspace

```agda
im-uniformly-continuous-map-inhabited-totally-bounded-Metric-Space :
  {l1 l2 l3 l4 l5 : Level} →
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  (f : uniformly-continuous-map-Metric-Space X Y) →
  is-totally-bounded-Metric-Space l5 X →
  is-inhabited (type-Metric-Space X) →
  inhabited-totally-bounded-subspace-Metric-Space (l1 ⊔ l3) (l1 ⊔ l3 ⊔ l5) Y
im-uniformly-continuous-map-inhabited-totally-bounded-Metric-Space
  X Y f tbX |X| =
  ( ( subtype-im (map-uniformly-continuous-map-Metric-Space X Y f) ,
      is-totally-bounded-im-uniformly-continuous-map-is-totally-bounded-Metric-Space
        ( X)
        ( Y)
        ( tbX)
        ( f)) ,
    map-is-inhabited
      ( map-unit-im (map-uniformly-continuous-map-Metric-Space X Y f))
      ( |X|))
```

### The image of an inhabited totally bounded subspace of a metric space under a uniformly continuous map is an inhabited totally bounded subspace

```agda
im-uniformly-continuous-map-inhabited-totally-bounded-subspace-Metric-Space :
  {l1 l2 l3 l4 l5 l6 : Level} →
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  (f : uniformly-continuous-map-Metric-Space X Y) →
  inhabited-totally-bounded-subspace-Metric-Space l5 l6 X →
  inhabited-totally-bounded-subspace-Metric-Space
    ( l1 ⊔ l3 ⊔ l5)
    ( l1 ⊔ l3 ⊔ l5 ⊔ l6)
    ( Y)
im-uniformly-continuous-map-inhabited-totally-bounded-subspace-Metric-Space
  X Y f ((S , tbS) , |S|) =
  im-uniformly-continuous-map-inhabited-totally-bounded-Metric-Space
    ( subspace-Metric-Space X S)
    ( Y)
    ( comp-uniformly-continuous-map-Metric-Space
      ( subspace-Metric-Space X S)
      ( X)
      ( Y)
      ( f)
      ( uniformly-continuous-inclusion-subspace-Metric-Space X S))
    ( tbS)
    ( |S|)
```

### Inhabited, totally bounded subspaces of metric spaces are closed under cartesian products

```agda
product-inhabited-totally-bounded-subspace-Metric-Space :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} →
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  (S : inhabited-totally-bounded-subspace-Metric-Space l5 l6 X) →
  (T : inhabited-totally-bounded-subspace-Metric-Space l7 l8 Y) →
  inhabited-totally-bounded-subspace-Metric-Space
    ( l5 ⊔ l7)
    ( l1 ⊔ l3 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
    ( product-Metric-Space X Y)
product-inhabited-totally-bounded-subspace-Metric-Space
  X Y (S , |S|) (T , |T|) =
  ( product-totally-bounded-subspace-Metric-Space X Y S T ,
    map-is-inhabited
      ( map-inv-equiv
        ( equiv-product-subtype
          ( subset-totally-bounded-subspace-Metric-Space X S)
          ( subset-totally-bounded-subspace-Metric-Space Y T)))
      ( is-inhabited-Σ |S| (λ _ → |T|)))
```

### It is decidable whether or not a totally bounded subspace of a metric space is inhabited

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (S : totally-bounded-subspace-Metric-Space l3 l4 X)
  where

  abstract
    is-inhabited-or-empty-totally-bounded-subspace-Metric-Space :
      is-inhabited-or-empty (type-totally-bounded-subspace-Metric-Space X S)
    is-inhabited-or-empty-totally-bounded-subspace-Metric-Space =
      rec-trunc-Prop
        ( is-inhabited-or-empty-Prop _)
        ( λ M →
          is-inhabited-or-empty-type-is-inhabited-or-empty-net-Metric-Space
            ( subspace-totally-bounded-subspace-Metric-Space X S)
            ( one-ℚ⁺)
            ( M one-ℚ⁺))
        ( is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space X S)
```
