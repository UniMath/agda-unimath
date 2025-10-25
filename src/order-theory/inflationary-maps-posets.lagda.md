# Inflationary maps on a poset

```agda
module order-theory.inflationary-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.inflationary-maps-preorders
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map $f : P → P$ on a [poset](order-theory.posets.md) $P$ is said to be an
{{#concept "inflationary map" Disambiguation="poset" Agda=inflationary-map-Poset}}
if the inequality

$$
  x ≤ f(x)
$$

holds for any element $x : P$. In other words, a map on a poset is inflationary
precisely when the map on its underlying [preorder](order-theory.preorders.md)
is [inflationary](order-theory.inflationary-maps-preorders.md). If $f$ is also
[order preserving](order-theory.order-preserving-maps-posets.md) we say that $f$
is an
{{#concept "inflationary morphism" Disambiguation="poset" Agda=inflationary-hom-Poset}}.

## Definitions

### The predicate of being an inflationary map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : type-Poset P → type-Poset P)
  where

  is-inflationary-prop-map-Poset :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-map-Poset =
    is-inflationary-prop-map-Preorder (preorder-Poset P) f

  is-inflationary-map-Poset :
    UU (l1 ⊔ l2)
  is-inflationary-map-Poset =
    is-inflationary-map-Preorder (preorder-Poset P) f

  is-prop-is-inflationary-map-Poset :
    is-prop is-inflationary-map-Poset
  is-prop-is-inflationary-map-Poset =
    is-prop-is-inflationary-map-Preorder (preorder-Poset P) f
```

### The type of inflationary maps on a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  inflationary-map-Poset :
    UU (l1 ⊔ l2)
  inflationary-map-Poset =
    inflationary-map-Preorder (preorder-Poset P)

module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : inflationary-map-Poset P)
  where

  map-inflationary-map-Poset :
    type-Poset P → type-Poset P
  map-inflationary-map-Poset =
    map-inflationary-map-Preorder (preorder-Poset P) f

  is-inflationary-inflationary-map-Poset :
    is-inflationary-map-Poset P map-inflationary-map-Poset
  is-inflationary-inflationary-map-Poset =
    is-inflationary-inflationary-map-Preorder (preorder-Poset P) f
```

### The predicate on order preserving maps of being inflationary

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : hom-Poset P P)
  where

  is-inflationary-prop-hom-Poset : Prop (l1 ⊔ l2)
  is-inflationary-prop-hom-Poset =
    is-inflationary-prop-hom-Preorder (preorder-Poset P) f

  is-inflationary-hom-Poset : UU (l1 ⊔ l2)
  is-inflationary-hom-Poset =
    is-inflationary-hom-Preorder (preorder-Poset P) f

  is-prop-is-inflationary-hom-Poset :
    is-prop is-inflationary-hom-Poset
  is-prop-is-inflationary-hom-Poset =
    is-prop-is-inflationary-hom-Preorder (preorder-Poset P) f
```

### The type of inflationary morphisms on a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  inflationary-hom-Poset : UU (l1 ⊔ l2)
  inflationary-hom-Poset =
    inflationary-hom-Preorder (preorder-Poset P)

module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : inflationary-hom-Poset P)
  where

  hom-inflationary-hom-Poset :
    hom-Poset P P
  hom-inflationary-hom-Poset =
    hom-inflationary-hom-Preorder (preorder-Poset P) f

  map-inflationary-hom-Poset :
    type-Poset P → type-Poset P
  map-inflationary-hom-Poset =
    map-inflationary-hom-Preorder (preorder-Poset P) f

  preserves-order-inflationary-hom-Poset :
    preserves-order-Poset P P map-inflationary-hom-Poset
  preserves-order-inflationary-hom-Poset =
    preserves-order-inflationary-hom-Preorder (preorder-Poset P) f

  is-inflationary-inflationary-hom-Poset :
    is-inflationary-map-Poset P map-inflationary-hom-Poset
  is-inflationary-inflationary-hom-Poset =
    is-inflationary-inflationary-hom-Preorder (preorder-Poset P) f

  inflationary-map-inflationary-hom-Poset :
    inflationary-map-Poset P
  inflationary-map-inflationary-hom-Poset =
    inflationary-map-inflationary-hom-Preorder (preorder-Poset P) f
```
