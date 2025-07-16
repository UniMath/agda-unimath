# Cocartesian morphisms of arrows

```agda
module synthetic-homotopy-theory.cocartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pullback-property-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A [morphism of arrows](foundation.morphisms-arrows.md) `h : f → g` is said to be
{{#concept "cocartesian" Disambiguation="morphism of arrows" Agda=is-cocartesian-hom-arrow}}
if the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
        i
    A -----> X
    |        |
  f |   h    | g
    ∨        ∨
    B -----> Y
        j
```

is a [pushout](synthetic-homotopy-theory.pushouts.md) square. In this instance,
we also say that `g` is a
{{#concept "cobase change" Disambiguation="maps of types"}} of `f`.

## Definitions

### The predicate of being a cocartesian morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-cocartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cocartesian-hom-arrow =
    is-pushout f (map-domain-hom-arrow f g h) (cocone-hom-arrow f g h)

  is-prop-is-cocartesian-hom-arrow : is-prop is-cocartesian-hom-arrow
  is-prop-is-cocartesian-hom-arrow =
    is-prop-is-pushout f (map-domain-hom-arrow f g h) (cocone-hom-arrow f g h)

  is-cocartesian-hom-arrow-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-cocartesian-hom-arrow-Prop = is-cocartesian-hom-arrow
  pr2 is-cocartesian-hom-arrow-Prop = is-prop-is-cocartesian-hom-arrow
```

### The type of cocartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  cocartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocartesian-hom-arrow = Σ (hom-arrow f g) (is-cocartesian-hom-arrow f g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : cocartesian-hom-arrow f g)
  where

  hom-arrow-cocartesian-hom-arrow : hom-arrow f g
  hom-arrow-cocartesian-hom-arrow = pr1 h

  is-cocartesian-cocartesian-hom-arrow :
    is-cocartesian-hom-arrow f g hom-arrow-cocartesian-hom-arrow
  is-cocartesian-cocartesian-hom-arrow = pr2 h

  map-domain-cocartesian-hom-arrow : A → X
  map-domain-cocartesian-hom-arrow =
    map-domain-hom-arrow f g hom-arrow-cocartesian-hom-arrow

  map-codomain-cocartesian-hom-arrow : B → Y
  map-codomain-cocartesian-hom-arrow =
    map-codomain-hom-arrow f g hom-arrow-cocartesian-hom-arrow

  coh-cocartesian-hom-arrow :
    coherence-square-maps
      ( map-domain-cocartesian-hom-arrow)
      ( f)
      ( g)
      ( map-codomain-cocartesian-hom-arrow)
  coh-cocartesian-hom-arrow =
    coh-hom-arrow f g hom-arrow-cocartesian-hom-arrow

  cocone-cocartesian-hom-arrow :
    cocone f map-domain-cocartesian-hom-arrow Y
  cocone-cocartesian-hom-arrow =
    cocone-hom-arrow f g hom-arrow-cocartesian-hom-arrow

  universal-property-cocartesian-hom-arrow :
    universal-property-pushout
      ( f)
      ( map-domain-cocartesian-hom-arrow)
      ( cocone-cocartesian-hom-arrow)
  universal-property-cocartesian-hom-arrow =
    universal-property-pushout-is-pushout
      ( f)
      ( map-domain-cocartesian-hom-arrow)
      ( cocone-cocartesian-hom-arrow)
      ( is-cocartesian-cocartesian-hom-arrow)
```

### The cartesian morphism on precomposition maps

```agda
module _
  {l1 l2 l3 l4 l : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : cocartesian-hom-arrow f g) (S : UU l)
  where

  precomp-cocartesian-hom-arrow : hom-arrow (precomp g S) (precomp f S)
  precomp-cocartesian-hom-arrow =
    precomp-hom-arrow f g (hom-arrow-cocartesian-hom-arrow f g α) S

  abstract
    is-cartesian-precomp-cocartesian-hom-arrow :
      is-cartesian-hom-arrow
        ( precomp g S)
        ( precomp f S)
        ( precomp-cocartesian-hom-arrow)
    is-cartesian-precomp-cocartesian-hom-arrow =
      is-pullback-swap-cone
        ( precomp f S)
        ( precomp (map-domain-cocartesian-hom-arrow f g α) S)
        ( cone-hom-arrow
          ( precomp (map-codomain-cocartesian-hom-arrow f g α) S)
          ( precomp (map-domain-cocartesian-hom-arrow f g α) S)
          ( transpose-precomp-hom-arrow f g
            ( hom-arrow-cocartesian-hom-arrow f g α)
            ( S)))
        ( pullback-property-pushout-is-pushout
          ( f)
          ( map-domain-cocartesian-hom-arrow f g α)
          ( cocone-cocartesian-hom-arrow f g α)
          ( is-cocartesian-cocartesian-hom-arrow f g α) S)

  precomp-cartesian-hom-arrow-cocartesian-hom-arrow :
    cartesian-hom-arrow (precomp g S) (precomp f S)
  precomp-cartesian-hom-arrow-cocartesian-hom-arrow =
    ( precomp-cocartesian-hom-arrow ,
      is-cartesian-precomp-cocartesian-hom-arrow)
```

## See also

- [Cartesian morphisms of arrows](foundation.cartesian-morphisms-arrows.md) for
  the dual.
