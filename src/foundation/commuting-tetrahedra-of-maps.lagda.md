# Commuting tetrahedra of maps

```agda
module foundation.commuting-tetrahedra-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
```

</details>

## Idea

A {{#concept "commuting tetrahedron of maps" Agda=coherence-tetrahedron-maps}}
is a commuting diagram of the form

```text
  A ----------> B
  |  \       ∧  |
  |    \   /    |
  |      /      |
  |    /   \    |
  ∨  /       ∨  ∨
  X ----------> Y.
```

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A → X) (right : B → Y) (bottom : X → Y)
  (diagonal-up : X → B) (diagonal-down : A → Y)
  (upper-left : coherence-triangle-maps top diagonal-up left)
  (lower-right : coherence-triangle-maps bottom right diagonal-up)
  (upper-right : coherence-triangle-maps diagonal-down right top)
  (lower-left : coherence-triangle-maps diagonal-down bottom left)
  where

  coherence-tetrahedron-maps : UU (l1 ⊔ l4)
  coherence-tetrahedron-maps =
    ( upper-right ∙h (right ·l upper-left)) ~
    ( lower-left ∙h (lower-right ·r left))

  coherence-tetrahedron-maps' : UU (l1 ⊔ l4)
  coherence-tetrahedron-maps' =
    ( lower-left ∙h (lower-right ·r left)) ~
    ( upper-right ∙h (right ·l upper-left))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A → X) (right : B → Y) (bottom : X → Y)
  (diagonal-up : X → B) (diagonal-down : A → Y)
  (upper-left : coherence-triangle-maps' top diagonal-up left)
  (lower-right : coherence-triangle-maps' bottom right diagonal-up)
  (upper-right : coherence-triangle-maps' diagonal-down right top)
  (lower-left : coherence-triangle-maps' diagonal-down bottom left)
  where

  coherence-reverse-tetrahedron-maps : UU (l1 ⊔ l4)
  coherence-reverse-tetrahedron-maps =
    ( (right ·l upper-left) ∙h upper-right) ~
    ( (lower-right ·r left) ∙h lower-left)

  coherence-reverse-tetrahedron-maps' : UU (l1 ⊔ l4)
  coherence-reverse-tetrahedron-maps' =
    ( (lower-right ·r left) ∙h lower-left) ~
    ( (right ·l upper-left) ∙h upper-right)
```
