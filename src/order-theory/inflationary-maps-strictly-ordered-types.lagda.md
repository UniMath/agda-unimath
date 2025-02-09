# Inflationary maps on a strictly ordered type

```agda
module order-theory.inflationary-maps-strictly-ordered-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-ordered-types
```

</details>

## Idea

A map $f : P → P$ on a
[strictly ordered type](order-theory.strictly-ordered-types.md) $P$ is said to
be an
{{#concept "inflationary map" Disambiguation="strictly ordered type" Agda=inflationary-map-Strictly-Ordered-Type}}
if the inequality

$$
  x < f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.order-preserving-maps-strictly-ordered-types.md)
we say that $f$ is an
{{#concept "inflationary morphism" Disambiguation="strictly ordered type" Agda=inflationary-hom-Strictly-Ordered-Type}}.

## Definitions

### The predicate of being an inflationary map

```agda
module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  (f : type-Strictly-Ordered-Type P → type-Strictly-Ordered-Type P)
  where

  is-inflationary-prop-map-Strictly-Ordered-Type :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-map-Strictly-Ordered-Type =
    Π-Prop
      ( type-Strictly-Ordered-Type P)
      ( λ x → le-prop-Strictly-Ordered-Type P x (f x))

  is-inflationary-map-Strictly-Ordered-Type :
    UU (l1 ⊔ l2)
  is-inflationary-map-Strictly-Ordered-Type =
    type-Prop is-inflationary-prop-map-Strictly-Ordered-Type

  is-prop-is-inflationary-map-Strictly-Ordered-Type :
    is-prop is-inflationary-map-Strictly-Ordered-Type
  is-prop-is-inflationary-map-Strictly-Ordered-Type =
    is-prop-type-Prop is-inflationary-prop-map-Strictly-Ordered-Type
```

### The type of inflationary maps on a strictly ordered type

```agda
module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  where

  inflationary-map-Strictly-Ordered-Type :
    UU (l1 ⊔ l2)
  inflationary-map-Strictly-Ordered-Type =
    type-subtype (is-inflationary-prop-map-Strictly-Ordered-Type P)

module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  (f : inflationary-map-Strictly-Ordered-Type P)
  where

  map-inflationary-map-Strictly-Ordered-Type :
    type-Strictly-Ordered-Type P → type-Strictly-Ordered-Type P
  map-inflationary-map-Strictly-Ordered-Type =
    pr1 f

  is-inflationary-inflationary-map-Strictly-Ordered-Type :
    is-inflationary-map-Strictly-Ordered-Type P
      ( map-inflationary-map-Strictly-Ordered-Type)
  is-inflationary-inflationary-map-Strictly-Ordered-Type =
    pr2 f
```

### The predicate on order preserving maps of being inflationary

```agda
module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  (f : hom-Strictly-Ordered-Type P P)
  where

  is-inflationary-prop-hom-Strictly-Ordered-Type :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-hom-Strictly-Ordered-Type =
    is-inflationary-prop-map-Strictly-Ordered-Type P
      ( map-hom-Strictly-Ordered-Type P P f)

  is-inflationary-hom-Strictly-Ordered-Type :
    UU (l1 ⊔ l2)
  is-inflationary-hom-Strictly-Ordered-Type =
    is-inflationary-map-Strictly-Ordered-Type P
      ( map-hom-Strictly-Ordered-Type P P f)

  is-prop-is-inflationary-hom-Strictly-Ordered-Type :
    is-prop is-inflationary-hom-Strictly-Ordered-Type
  is-prop-is-inflationary-hom-Strictly-Ordered-Type =
    is-prop-is-inflationary-map-Strictly-Ordered-Type P
      ( map-hom-Strictly-Ordered-Type P P f)
```

### The type of inflationary morphisms on a strictly ordered type

```agda
module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  where

  inflationary-hom-Strictly-Ordered-Type :
    UU (l1 ⊔ l2)
  inflationary-hom-Strictly-Ordered-Type =
    type-subtype (is-inflationary-prop-hom-Strictly-Ordered-Type P)

module _
  {l1 l2 : Level} (P : Strictly-Ordered-Type l1 l2)
  (f : inflationary-hom-Strictly-Ordered-Type P)
  where

  hom-inflationary-hom-Strictly-Ordered-Type :
    hom-Strictly-Ordered-Type P P
  hom-inflationary-hom-Strictly-Ordered-Type =
    pr1 f

  map-inflationary-hom-Strictly-Ordered-Type :
    type-Strictly-Ordered-Type P → type-Strictly-Ordered-Type P
  map-inflationary-hom-Strictly-Ordered-Type =
    map-hom-Strictly-Ordered-Type P P hom-inflationary-hom-Strictly-Ordered-Type

  preserves-order-inflationary-hom-Strictly-Ordered-Type :
    preserves-strict-order-map-Strictly-Ordered-Type P P
      ( map-inflationary-hom-Strictly-Ordered-Type)
  preserves-order-inflationary-hom-Strictly-Ordered-Type =
    preserves-strict-order-hom-Strictly-Ordered-Type P P
      ( hom-inflationary-hom-Strictly-Ordered-Type)

  is-inflationary-inflationary-hom-Strictly-Ordered-Type :
    is-inflationary-map-Strictly-Ordered-Type P
      ( map-inflationary-hom-Strictly-Ordered-Type)
  is-inflationary-inflationary-hom-Strictly-Ordered-Type =
    pr2 f

  inflationary-map-inflationary-hom-Strictly-Ordered-Type :
    inflationary-map-Strictly-Ordered-Type P
  pr1 inflationary-map-inflationary-hom-Strictly-Ordered-Type =
    map-inflationary-hom-Strictly-Ordered-Type
  pr2 inflationary-map-inflationary-hom-Strictly-Ordered-Type =
    is-inflationary-inflationary-hom-Strictly-Ordered-Type
```
