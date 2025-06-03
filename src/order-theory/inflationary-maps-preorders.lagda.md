# Inflationary maps on a preorder

```agda
module order-theory.inflationary-maps-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.preorders
```

</details>

## Idea

A map $f : P → P$ on a [preorder](order-theory.preorders.md) $P$ is said to be
an
{{#concept "inflationary map" Disambiguation="preorder" Agda=inflationary-map-Preorder}}
if the inequality

$$
  x ≤ f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.order-preserving-maps-preorders.md) we say that
$f$ is an
{{#concept "inflationary morphism" Disambiguation="preorder" Agda=inflationary-hom-Preorder}}.

## Definitions

### The predicate of being an inflationary map

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : type-Preorder P → type-Preorder P)
  where

  is-inflationary-prop-map-Preorder :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-map-Preorder =
    Π-Prop (type-Preorder P) (λ x → leq-prop-Preorder P x (f x))

  is-inflationary-map-Preorder :
    UU (l1 ⊔ l2)
  is-inflationary-map-Preorder =
    type-Prop is-inflationary-prop-map-Preorder

  is-prop-is-inflationary-map-Preorder :
    is-prop is-inflationary-map-Preorder
  is-prop-is-inflationary-map-Preorder =
    is-prop-type-Prop is-inflationary-prop-map-Preorder
```

### The type of inflationary maps on a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  inflationary-map-Preorder :
    UU (l1 ⊔ l2)
  inflationary-map-Preorder =
    type-subtype (is-inflationary-prop-map-Preorder P)

module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : inflationary-map-Preorder P)
  where

  map-inflationary-map-Preorder :
    type-Preorder P → type-Preorder P
  map-inflationary-map-Preorder =
    pr1 f

  is-inflationary-inflationary-map-Preorder :
    is-inflationary-map-Preorder P map-inflationary-map-Preorder
  is-inflationary-inflationary-map-Preorder =
    pr2 f
```

### The predicate on order preserving maps of being inflationary

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : hom-Preorder P P)
  where

  is-inflationary-prop-hom-Preorder : Prop (l1 ⊔ l2)
  is-inflationary-prop-hom-Preorder =
    is-inflationary-prop-map-Preorder P (map-hom-Preorder P P f)

  is-inflationary-hom-Preorder : UU (l1 ⊔ l2)
  is-inflationary-hom-Preorder =
    is-inflationary-map-Preorder P (map-hom-Preorder P P f)

  is-prop-is-inflationary-hom-Preorder :
    is-prop is-inflationary-hom-Preorder
  is-prop-is-inflationary-hom-Preorder =
    is-prop-is-inflationary-map-Preorder P (map-hom-Preorder P P f)
```

### The type of inflationary morphisms on a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  inflationary-hom-Preorder : UU (l1 ⊔ l2)
  inflationary-hom-Preorder =
    type-subtype (is-inflationary-prop-hom-Preorder P)

module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : inflationary-hom-Preorder P)
  where

  hom-inflationary-hom-Preorder :
    hom-Preorder P P
  hom-inflationary-hom-Preorder =
    pr1 f

  map-inflationary-hom-Preorder :
    type-Preorder P → type-Preorder P
  map-inflationary-hom-Preorder =
    map-hom-Preorder P P hom-inflationary-hom-Preorder

  preserves-order-inflationary-hom-Preorder :
    preserves-order-Preorder P P map-inflationary-hom-Preorder
  preserves-order-inflationary-hom-Preorder =
    preserves-order-hom-Preorder P P hom-inflationary-hom-Preorder

  is-inflationary-inflationary-hom-Preorder :
    is-inflationary-map-Preorder P map-inflationary-hom-Preorder
  is-inflationary-inflationary-hom-Preorder =
    pr2 f

  inflationary-map-inflationary-hom-Preorder :
    inflationary-map-Preorder P
  pr1 inflationary-map-inflationary-hom-Preorder =
    map-inflationary-hom-Preorder
  pr2 inflationary-map-inflationary-hom-Preorder =
    is-inflationary-inflationary-hom-Preorder
```
