# Closed interval preserving maps between total orders

```agda
module order-theory.closed-interval-preserving-maps-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.images-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.closed-interval-preserving-maps-posets
open import order-theory.closed-intervals-total-orders
open import order-theory.total-orders
```

</details>

## Idea

A map between [total orders](order-theory.total-orders.md) `f : X → Y` is
{{#concept "closed interval preserving" Agda=is-closed-interval-map-Total-Order disambiguation="map between total orders"}}
if the [image](foundation.images-subtypes.md) of a
[closed interval](order-theory.closed-intervals-total-orders.md) in `X` is
always a closed interval in `Y`. Equivalently, it is a
[closed interval preserving map](order-theory.closed-interval-preserving-maps-posets.md)
on the underlying [posets](order-theory.posets.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Total-Order l1 l2) (Y : Total-Order l3 l4)
  (f : type-Total-Order X → type-Total-Order Y)
  where

  is-closed-interval-map-prop-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    ([c,d] : closed-interval-Total-Order Y) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-prop-Total-Order =
    is-closed-interval-map-prop-Poset
      ( poset-Total-Order X)
      ( poset-Total-Order Y)
      ( f)

  is-closed-interval-map-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    ([c,d] : closed-interval-Total-Order Y) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-Total-Order [a,b] [c,d] =
    type-Prop (is-closed-interval-map-prop-Total-Order [a,b] [c,d])
```
