# Cartesian morphisms of arrows

```agda
module foundation.cartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.morphisms-arrows
open import foundation.pullbacks
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.propositions
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

A [morphism of arrows](foundation.morphisms-arrows.md) `h : f → g` is said to be
{{#concept "cartesian" Disambiguation="morphism of arrows" Agda=is-cartesian-hom-arrow}}
if the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
        i
    A -----> X
    |        |
  f |   h    | g
    V        V
    B -----> Y
        j
```

is a [pullback](foundation.pullbacks.md) square.

## Definitions

### The predicate of being a cartesian morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-cartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cartesian-hom-arrow =
    is-pullback (map-codomain-hom-arrow f g h) g (cone-hom-arrow f g h)

  is-prop-is-cartesian-hom-arrow : is-prop is-cartesian-hom-arrow
  is-prop-is-cartesian-hom-arrow =
    is-prop-is-pullback (map-codomain-hom-arrow f g h) g (cone-hom-arrow f g h)

  is-cartesian-hom-arrow-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-cartesian-hom-arrow-Prop = is-cartesian-hom-arrow
  pr2 is-cartesian-hom-arrow-Prop = is-prop-is-cartesian-hom-arrow
```

### The type of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  cartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cartesian-hom-arrow = Σ (hom-arrow f g) (is-cartesian-hom-arrow f g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : cartesian-hom-arrow f g)
  where

  hom-arrow-cartesian-hom-arrow : hom-arrow f g
  hom-arrow-cartesian-hom-arrow = pr1 h

  is-cartesian-cartesian-hom-arrow :
    is-cartesian-hom-arrow f g hom-arrow-cartesian-hom-arrow
  is-cartesian-cartesian-hom-arrow = pr2 h

  map-domain-cartesian-hom-arrow : A → X
  map-domain-cartesian-hom-arrow =
    map-domain-hom-arrow f g hom-arrow-cartesian-hom-arrow

  map-codomain-cartesian-hom-arrow : B → Y
  map-codomain-cartesian-hom-arrow =
    map-codomain-hom-arrow f g hom-arrow-cartesian-hom-arrow

  coh-cartesian-hom-arrow :
    coherence-square-maps
      ( map-domain-cartesian-hom-arrow)
      ( f)
      ( g)
      ( map-codomain-cartesian-hom-arrow)
  coh-cartesian-hom-arrow =
    coh-hom-arrow f g hom-arrow-cartesian-hom-arrow

  cone-cartesian-hom-arrow :
    cone map-codomain-cartesian-hom-arrow g A
  cone-cartesian-hom-arrow =
    cone-hom-arrow f g hom-arrow-cartesian-hom-arrow

  universal-property-cartesian-hom-arrow :
    universal-property-pullback
      ( map-codomain-cartesian-hom-arrow)
      ( g)
      ( cone-cartesian-hom-arrow)
  universal-property-cartesian-hom-arrow =
    universal-property-pullback-is-pullback
      ( map-codomain-cartesian-hom-arrow)
      ( g)
      ( cone-cartesian-hom-arrow)
      ( is-cartesian-cartesian-hom-arrow)
```

### Cartesian morphisms of arrows arising from fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  fiber-cartesian-hom-arrow :
    cartesian-hom-arrow (terminal-map (fiber f y)) f
  pr1 fiber-cartesian-hom-arrow =
    hom-arrow-cone (point y) f (swap-cone f (point y) (cone-fiber f y))
  pr2 fiber-cartesian-hom-arrow =
    is-pullback-swap-cone f (point y)
      ( cone-fiber f y)
      ( is-pullback-cone-fiber f y)
```

## See also

- [Cocartesian morphisms of arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.md)
  for the dual.
