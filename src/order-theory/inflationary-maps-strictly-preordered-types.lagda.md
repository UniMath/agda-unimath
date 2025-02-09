# Inflationary maps on a strictly preordered type

```agda
module order-theory.inflationary-maps-strictly-preordered-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-preordered-types
```

</details>

## Idea

A map $f : P → P$ on a
[strictly preordered type](order-theory.strictly-preordered-types.md) $P$ is
said to be an
{{#concept "inflationary map" Disambiguation="strictly preordered type" Agda=inflationary-map-Strictly-Preordered-Type}}
if the inequality

$$
  x < f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.strict-order-preserving-maps.md) we say that $f$
is an
{{#concept "inflationary morphism" Disambiguation="strictly preordered type" Agda=inflationary-hom-Strictly-Preordered-Type}}.

## Definitions

### The predicate of being an inflationary map

```agda
module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  (f : type-Strictly-Preordered-Type P → type-Strictly-Preordered-Type P)
  where

  is-inflationary-prop-map-Strictly-Preordered-Type :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-map-Strictly-Preordered-Type =
    Π-Prop
      ( type-Strictly-Preordered-Type P)
      ( λ x → le-prop-Strictly-Preordered-Type P x (f x))

  is-inflationary-map-Strictly-Preordered-Type :
    UU (l1 ⊔ l2)
  is-inflationary-map-Strictly-Preordered-Type =
    type-Prop is-inflationary-prop-map-Strictly-Preordered-Type

  is-prop-is-inflationary-map-Strictly-Preordered-Type :
    is-prop is-inflationary-map-Strictly-Preordered-Type
  is-prop-is-inflationary-map-Strictly-Preordered-Type =
    is-prop-type-Prop is-inflationary-prop-map-Strictly-Preordered-Type
```

### The type of inflationary maps on a strictly preordered type

```agda
module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  where

  inflationary-map-Strictly-Preordered-Type :
    UU (l1 ⊔ l2)
  inflationary-map-Strictly-Preordered-Type =
    type-subtype (is-inflationary-prop-map-Strictly-Preordered-Type P)

module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  (f : inflationary-map-Strictly-Preordered-Type P)
  where

  map-inflationary-map-Strictly-Preordered-Type :
    type-Strictly-Preordered-Type P → type-Strictly-Preordered-Type P
  map-inflationary-map-Strictly-Preordered-Type =
    pr1 f

  is-inflationary-inflationary-map-Strictly-Preordered-Type :
    is-inflationary-map-Strictly-Preordered-Type P
      ( map-inflationary-map-Strictly-Preordered-Type)
  is-inflationary-inflationary-map-Strictly-Preordered-Type =
    pr2 f
```

### The predicate on order preserving maps of being inflationary

```agda
module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  (f : hom-Strictly-Preordered-Type P P)
  where

  is-inflationary-prop-hom-Strictly-Preordered-Type :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-hom-Strictly-Preordered-Type =
    is-inflationary-prop-map-Strictly-Preordered-Type P
      ( map-hom-Strictly-Preordered-Type P P f)

  is-inflationary-hom-Strictly-Preordered-Type :
    UU (l1 ⊔ l2)
  is-inflationary-hom-Strictly-Preordered-Type =
    is-inflationary-map-Strictly-Preordered-Type P
      ( map-hom-Strictly-Preordered-Type P P f)

  is-prop-is-inflationary-hom-Strictly-Preordered-Type :
    is-prop is-inflationary-hom-Strictly-Preordered-Type
  is-prop-is-inflationary-hom-Strictly-Preordered-Type =
    is-prop-is-inflationary-map-Strictly-Preordered-Type P
      ( map-hom-Strictly-Preordered-Type P P f)
```

### The type of inflationary morphisms on a strictly preordered type

```agda
module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  where

  inflationary-hom-Strictly-Preordered-Type :
    UU (l1 ⊔ l2)
  inflationary-hom-Strictly-Preordered-Type =
    type-subtype (is-inflationary-prop-hom-Strictly-Preordered-Type P)

module _
  {l1 l2 : Level} (P : Strictly-Preordered-Type l1 l2)
  (f : inflationary-hom-Strictly-Preordered-Type P)
  where

  hom-inflationary-hom-Strictly-Preordered-Type :
    hom-Strictly-Preordered-Type P P
  hom-inflationary-hom-Strictly-Preordered-Type =
    pr1 f

  map-inflationary-hom-Strictly-Preordered-Type :
    type-Strictly-Preordered-Type P → type-Strictly-Preordered-Type P
  map-inflationary-hom-Strictly-Preordered-Type =
    map-hom-Strictly-Preordered-Type P P hom-inflationary-hom-Strictly-Preordered-Type

  preserves-order-inflationary-hom-Strictly-Preordered-Type :
    preserves-strict-order-map-Strictly-Preordered-Type P P
      ( map-inflationary-hom-Strictly-Preordered-Type)
  preserves-order-inflationary-hom-Strictly-Preordered-Type =
    preserves-strict-order-hom-Strictly-Preordered-Type P P
      ( hom-inflationary-hom-Strictly-Preordered-Type)

  is-inflationary-inflationary-hom-Strictly-Preordered-Type :
    is-inflationary-map-Strictly-Preordered-Type P
      ( map-inflationary-hom-Strictly-Preordered-Type)
  is-inflationary-inflationary-hom-Strictly-Preordered-Type =
    pr2 f

  inflationary-map-inflationary-hom-Strictly-Preordered-Type :
    inflationary-map-Strictly-Preordered-Type P
  pr1 inflationary-map-inflationary-hom-Strictly-Preordered-Type =
    map-inflationary-hom-Strictly-Preordered-Type
  pr2 inflationary-map-inflationary-hom-Strictly-Preordered-Type =
    is-inflationary-inflationary-hom-Strictly-Preordered-Type
```
