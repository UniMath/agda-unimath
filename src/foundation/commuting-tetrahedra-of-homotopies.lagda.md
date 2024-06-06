# Commuting tetrahedra of homotopies

```agda
module foundation.commuting-tetrahedra-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.universe-levels

open import foundation-core.homotopies
```

</details>

## Idea

A
{{#concept "commuting tetrahedron of homotopies" Agda=coherence-tetrahedron-homotopies}}
is a commuting diagram of the form

```text
             top
       f ──────────> g
       │  ╲       ∧  │
       │    ╲   ╱    │
  left │      ╱      │ right
       │    ╱   ╲    │
       ∨  ╱       ∨  ∨
       h ──────────> i.
            bottom
```

where `f`, `g`, `h`, and `i` are functions.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  (diagonal-up : h ~ g) (diagonal-down : f ~ i)
  (upper-left : coherence-triangle-homotopies top diagonal-up left)
  (lower-right : coherence-triangle-homotopies bottom right diagonal-up)
  (upper-right : coherence-triangle-homotopies diagonal-down right top)
  (lower-left : coherence-triangle-homotopies diagonal-down bottom left)
  where

  coherence-tetrahedron-homotopies : UU (l1 ⊔ l2)
  coherence-tetrahedron-homotopies =
    ( ( upper-right) ∙h
      ( right-whisker-concat-coherence-triangle-homotopies
        ( top)
        ( diagonal-up)
        ( left)
        ( upper-left)
        ( right))) ~
    ( ( lower-left) ∙h
      ( left-whisker-concat-coherence-triangle-homotopies
        ( left)
        ( bottom)
        ( right)
        ( diagonal-up)
        ( lower-right)) ∙h
      ( assoc-htpy left diagonal-up right))

  coherence-tetrahedron-homotopies' : UU (l1 ⊔ l2)
  coherence-tetrahedron-homotopies' =
    ( ( lower-left) ∙h
      ( left-whisker-concat-coherence-triangle-homotopies
        ( left)
        ( bottom)
        ( right)
        ( diagonal-up)
        ( lower-right)) ∙h
      ( assoc-htpy left diagonal-up right)) ~
    ( ( upper-right) ∙h
      ( right-whisker-concat-coherence-triangle-homotopies
        ( top)
        ( diagonal-up)
        ( left)
        ( upper-left)
        ( right)))
```
