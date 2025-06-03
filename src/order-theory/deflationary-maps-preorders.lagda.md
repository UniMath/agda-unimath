# Deflationary maps on a preorder

```agda
module order-theory.deflationary-maps-preorders where
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

A map $f : P → P$ on a [preorder](order-theory.preorders.md) $P$ is said to be a
{{#concept "deflationary map" Disambiguation="preorder" Agda=deflationary-map-Preorder}}
if the inequality

$$
  f(x) ≤ x
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.order-preserving-maps-preorders.md) we say that
$f$ is a
{{#concept "deflationary morphism" Disambiguation="preorder" Agda=deflationary-hom-Preorder}}.

## Definitions

### The predicate of being a deflationary map

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : type-Preorder P → type-Preorder P)
  where

  is-deflationary-prop-map-Preorder :
    Prop (l1 ⊔ l2)
  is-deflationary-prop-map-Preorder =
    Π-Prop (type-Preorder P) (λ x → leq-prop-Preorder P (f x) x)

  is-deflationary-map-Preorder :
    UU (l1 ⊔ l2)
  is-deflationary-map-Preorder =
    type-Prop is-deflationary-prop-map-Preorder

  is-prop-is-deflationary-map-Preorder :
    is-prop is-deflationary-map-Preorder
  is-prop-is-deflationary-map-Preorder =
    is-prop-type-Prop is-deflationary-prop-map-Preorder
```

### The type of deflationary maps on a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  deflationary-map-Preorder :
    UU (l1 ⊔ l2)
  deflationary-map-Preorder =
    type-subtype (is-deflationary-prop-map-Preorder P)

module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : deflationary-map-Preorder P)
  where

  map-deflationary-map-Preorder :
    type-Preorder P → type-Preorder P
  map-deflationary-map-Preorder =
    pr1 f

  is-deflationary-deflationary-map-Preorder :
    is-deflationary-map-Preorder P map-deflationary-map-Preorder
  is-deflationary-deflationary-map-Preorder =
    pr2 f
```

### The predicate on order preserving maps of being deflationary

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : hom-Preorder P P)
  where

  is-deflationary-prop-hom-Preorder : Prop (l1 ⊔ l2)
  is-deflationary-prop-hom-Preorder =
    is-deflationary-prop-map-Preorder P (map-hom-Preorder P P f)

  is-deflationary-hom-Preorder : UU (l1 ⊔ l2)
  is-deflationary-hom-Preorder =
    is-deflationary-map-Preorder P (map-hom-Preorder P P f)

  is-prop-is-deflationary-hom-Preorder :
    is-prop is-deflationary-hom-Preorder
  is-prop-is-deflationary-hom-Preorder =
    is-prop-is-deflationary-map-Preorder P (map-hom-Preorder P P f)
```

### The type of deflationary morphisms on a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  deflationary-hom-Preorder : UU (l1 ⊔ l2)
  deflationary-hom-Preorder =
    type-subtype (is-deflationary-prop-hom-Preorder P)

module _
  {l1 l2 : Level} (P : Preorder l1 l2) (f : deflationary-hom-Preorder P)
  where

  hom-deflationary-hom-Preorder :
    hom-Preorder P P
  hom-deflationary-hom-Preorder =
    pr1 f

  map-deflationary-hom-Preorder :
    type-Preorder P → type-Preorder P
  map-deflationary-hom-Preorder =
    map-hom-Preorder P P hom-deflationary-hom-Preorder

  preserves-order-deflationary-hom-Preorder :
    preserves-order-Preorder P P map-deflationary-hom-Preorder
  preserves-order-deflationary-hom-Preorder =
    preserves-order-hom-Preorder P P hom-deflationary-hom-Preorder

  is-deflationary-deflationary-hom-Preorder :
    is-deflationary-map-Preorder P map-deflationary-hom-Preorder
  is-deflationary-deflationary-hom-Preorder =
    pr2 f

  deflationary-map-deflationary-hom-Preorder :
    deflationary-map-Preorder P
  pr1 deflationary-map-deflationary-hom-Preorder =
    map-deflationary-hom-Preorder
  pr2 deflationary-map-deflationary-hom-Preorder =
    is-deflationary-deflationary-hom-Preorder
```
