# Cocartesian morphisms of arrows

```agda
module synthetic-homotopy-theory.cocartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
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
    V        V
    B -----> Y
        j
```

is a [pushout square](synthetic-homotopy-theory.pushouts.md).

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
```
