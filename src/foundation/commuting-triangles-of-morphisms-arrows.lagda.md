# Commuting triangles of morphisms of arrows

```agda
module foundation.commuting-triangles-of-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies-morphisms-arrows
open import foundation.morphisms-arrows
open import foundation.universe-levels
```

</details>

## Idea

Consider a triangle of [morphisms of arrows](foundation.morphisms-arrows.md)

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

then we can ask that the triangle
{{#concept "commutes" Disambiguation="triangle of morphisms of arrows"}}

by asking for a [homotopy](foundation.homotopies-morphisms-arrows.md) of
morphisms of arrows

```text
  left ~ right ∘ top.
```

This is [equivalent](foundation-core.equivalences.md) to asking for a
[commuting prism of maps](foundation-core.commuting-prisms-of-maps.md), given
the square faces in the diagram

```text
        f
  ∙ ---------> ∙
  |\           |\
  | \          | \
  |  \         |  \
  |   ∨        |   ∨
  |    ∙ --- g ---> ∙
  |   /        |   /
  |  /         |  /
  | /          | /
  ∨∨           ∨∨
  ∙ ---------> ∙.
        h
```

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (left : hom-arrow f h) (right : hom-arrow g h) (top : hom-arrow f g)
  where

  coherence-triangle-hom-arrow : UU (l1 ⊔ l2 ⊔ l5 ⊔ l6)
  coherence-triangle-hom-arrow =
    htpy-hom-arrow f h left (comp-hom-arrow f g h right top)

  coherence-triangle-hom-arrow' : UU (l1 ⊔ l2 ⊔ l5 ⊔ l6)
  coherence-triangle-hom-arrow' =
    htpy-hom-arrow f h (comp-hom-arrow f g h right top) left
```
