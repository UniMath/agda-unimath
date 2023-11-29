# Cocartesian morphisms of arrows

```agda
module synthetic-homotopy-theory.cocartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-arrows
open import foundation.universe-levels
```

</details>

## Idea

A [morphism of arrows](foundation.morphisms-arrows.md) `h : f → g` is said to be
{{#concept "cocartesian" Disambiguation="morphism of arrows"}} if the
[commuting square](foundation-core.commuting-squares-of-maps.md)

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
```
