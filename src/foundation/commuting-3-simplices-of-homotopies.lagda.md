# Commuting `3`-simplices of homotopies

```agda
module foundation.commuting-3-simplices-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.universe-levels

open import foundation-core.homotopies
```

</details>

## Idea

A **commuting 3-simplex of homotopies** is a commuting diagram of the form

```text
  f ----------> g
  |  \       ^  |
  |    \   /    |
  |      /      |
  |    /   \    |
  V  /       v  V
  h ----------> i.
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

  coherence-3-simplex-homotopies : UU (l1 ⊔ l2)
  coherence-3-simplex-homotopies =
    ( upper-right ∙h
      left-whisk-htpy-coherence-triangle-homotopies
        ( diagonal-up)
        ( right)
        ( upper-left)) ~
    ( ( lower-left ∙h
        right-whisk-htpy-coherence-triangle-homotopies
          ( right)
          ( lower-right)
          ( left)) ∙h
      assoc-htpy left diagonal-up right)

  coherence-3-simplex-homotopies' : UU (l1 ⊔ l2)
  coherence-3-simplex-homotopies' =
    ( ( lower-left ∙h
        right-whisk-htpy-coherence-triangle-homotopies
          ( right)
          ( lower-right)
          ( left)) ∙h
      assoc-htpy left diagonal-up right) ~
    ( upper-right ∙h
      left-whisk-htpy-coherence-triangle-homotopies
        ( diagonal-up)
        ( right)
        ( upper-left))
```
