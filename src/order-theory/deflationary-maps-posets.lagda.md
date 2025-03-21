# Deflationary maps on a poset

```agda
module order-theory.deflationary-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.deflationary-maps-preorders
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A map $f : P → P$ on a [poset](order-theory.posets.md) $P$ is said to be a
{{#concept "deflationary map" Disambiguation="poset" Agda=deflationary-map-Poset}}
if the inequality

$$
  f(x) ≤ x
$$

holds for any element $x : P$. In other words, a map on a poset is deflationary
precisely when the map on its underlying [preorder](order-theory.preorders.md)
is [deflationary](order-theory.deflationary-maps-preorders.md). If $f$ is also
[order preserving](order-theory.order-preserving-maps-posets.md) we say that $f$
is a
{{#concept "deflationary morphism" Disambiguation="poset" Agda=deflationary-hom-Poset}}.

## Definitions

### The predicate of being a deflationary map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : type-Poset P → type-Poset P)
  where

  is-deflationary-prop-map-Poset :
    Prop (l1 ⊔ l2)
  is-deflationary-prop-map-Poset =
    is-deflationary-prop-map-Preorder (preorder-Poset P) f

  is-deflationary-map-Poset :
    UU (l1 ⊔ l2)
  is-deflationary-map-Poset =
    is-deflationary-map-Preorder (preorder-Poset P) f

  is-prop-is-deflationary-map-Poset :
    is-prop is-deflationary-map-Poset
  is-prop-is-deflationary-map-Poset =
    is-prop-is-deflationary-map-Preorder (preorder-Poset P) f
```

### The type of deflationary maps on a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  deflationary-map-Poset :
    UU (l1 ⊔ l2)
  deflationary-map-Poset =
    deflationary-map-Preorder (preorder-Poset P)

module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : deflationary-map-Poset P)
  where

  map-deflationary-map-Poset :
    type-Poset P → type-Poset P
  map-deflationary-map-Poset =
    map-deflationary-map-Preorder (preorder-Poset P) f

  is-deflationary-deflationary-map-Poset :
    is-deflationary-map-Poset P map-deflationary-map-Poset
  is-deflationary-deflationary-map-Poset =
    is-deflationary-deflationary-map-Preorder (preorder-Poset P) f
```

### The predicate on order preserving maps of being deflationary

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : hom-Poset P P)
  where

  is-deflationary-prop-hom-Poset : Prop (l1 ⊔ l2)
  is-deflationary-prop-hom-Poset =
    is-deflationary-prop-hom-Preorder (preorder-Poset P) f

  is-deflationary-hom-Poset : UU (l1 ⊔ l2)
  is-deflationary-hom-Poset =
    is-deflationary-hom-Preorder (preorder-Poset P) f

  is-prop-is-deflationary-hom-Poset :
    is-prop is-deflationary-hom-Poset
  is-prop-is-deflationary-hom-Poset =
    is-prop-is-deflationary-hom-Preorder (preorder-Poset P) f
```

### The type of deflationary morphisms on a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  deflationary-hom-Poset : UU (l1 ⊔ l2)
  deflationary-hom-Poset =
    deflationary-hom-Preorder (preorder-Poset P)

module _
  {l1 l2 : Level} (P : Poset l1 l2) (f : deflationary-hom-Poset P)
  where

  hom-deflationary-hom-Poset :
    hom-Poset P P
  hom-deflationary-hom-Poset =
    hom-deflationary-hom-Preorder (preorder-Poset P) f

  map-deflationary-hom-Poset :
    type-Poset P → type-Poset P
  map-deflationary-hom-Poset =
    map-deflationary-hom-Preorder (preorder-Poset P) f

  preserves-order-deflationary-hom-Poset :
    preserves-order-Poset P P map-deflationary-hom-Poset
  preserves-order-deflationary-hom-Poset =
    preserves-order-deflationary-hom-Preorder (preorder-Poset P) f

  is-deflationary-deflationary-hom-Poset :
    is-deflationary-map-Poset P map-deflationary-hom-Poset
  is-deflationary-deflationary-hom-Poset =
    is-deflationary-deflationary-hom-Preorder (preorder-Poset P) f

  deflationary-map-deflationary-hom-Poset :
    deflationary-map-Poset P
  deflationary-map-deflationary-hom-Poset =
    deflationary-map-deflationary-hom-Preorder (preorder-Poset P) f
```
