# Closed interval preserving maps between posets

```agda
module order-theory.closed-interval-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.images-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
open import order-theory.posets
```

</details>

## Idea

A map between [posets](order-theory.posets.md) `f : X → Y` is
{{#concept "closed interval preserving" Agda=is-closed-interval-map-Poset disambiguation="map between posets"}}
if the [image](foundation.images-subtypes.md) of a
[closed interval](order-theory.closed-intervals-posets.md) in `X` is
always a closed interval in `Y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Poset l1 l2) (Y : Poset l3 l4)
  (f : type-Poset X → type-Poset Y)
  where

  is-closed-interval-map-prop-Poset :
    ([a,b] : closed-interval-Poset X) →
    ([c,d] : closed-interval-Poset Y) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-prop-Poset [a,b] [c,d] =
    is-image-map-subtype-prop f
      ( subtype-closed-interval-Poset X [a,b])
      ( subtype-closed-interval-Poset Y [c,d])

  is-closed-interval-map-Poset :
    ([a,b] : closed-interval-Poset X) →
    ([c,d] : closed-interval-Poset Y) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-Poset [a,b] [c,d] =
    type-Prop (is-closed-interval-map-prop-Poset [a,b] [c,d])
```
