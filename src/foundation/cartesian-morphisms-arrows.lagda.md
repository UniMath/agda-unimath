# Cartesian morphisms of arrows

```agda
module foundation.cartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.propositions
open import foundation.pullbacks
open import foundation.universe-levels
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

is a [pullback](foundation.pullbacks.md) square, and we say that `f` is a
{{#concept "base change" Disambiguation="maps of types"}} of `g` along `j`.

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
```

## See also

- [Cocartesian morphisms of arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.md)
  for the dual.
