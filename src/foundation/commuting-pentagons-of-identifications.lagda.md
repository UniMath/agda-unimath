# Commuting pentagons of identifications

```agda
module foundation.commuting-pentagons-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A pentagon of [identifications](foundation-core.identity-types.md)

```text
               top
             x --- y
   top-left /       \ top-right
           /         \
          z           w
            \       /
  bottom-left \   / bottom-right
                v
```

is said to **commute** if there is an identification

```text
  top-left ∙ bottom-left ＝ (top ∙ top-right) ∙ bottom-right.
```

Such an identification is called a **coherence** of the pentagon.

## Definitions

### Commuting pentagons of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z w v : A}
  where

  coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) → UU l
  coherence-pentagon-identifications
    top top-left top-right bottom-left bottom-right =
    top-left ∙ bottom-left ＝ (top ∙ top-right) ∙ bottom-right
```

### Reflections of commuting pentagons of identifications

A pentagon may be reflected along an axis connecting an edge with its opposing
vertex. For example, we may reflect a pentagon

```text
               top
             x --- y
   top-left /       \ top-right
           /         \
          z           w
            \       /
  bottom-left \   / bottom-right
                v
```

along the axis connecting `top` and `v` to get

```text
               top⁻¹
              y --- x
   top-right /       \ top-left
            /         \
           w           z
             \       /
  bottom-right \   / bottom-left
                 v .
```

The reflections are named after the edge which the axis passes through, so the
above example is `reflect-top-coherence-pentagon-identifications`.

```agda
module _
  {l : Level} {A : UU l} {x y z w v : A}
  where

  reflect-top-coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) →
    coherence-pentagon-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( bottom-left)
      ( bottom-right) →
    coherence-pentagon-identifications
      ( inv top)
      ( top-right)
      ( top-left)
      ( bottom-right)
      ( bottom-left)
  reflect-top-coherence-pentagon-identifications
    refl top-left top-right bottom-left bottom-right H = inv H

  reflect-top-left-coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) →
    coherence-pentagon-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( bottom-left)
      ( bottom-right) →
    coherence-pentagon-identifications
      ( bottom-left)
      ( inv top-left)
      ( inv bottom-right)
      ( top)
      ( inv top-right)
  reflect-top-left-coherence-pentagon-identifications
    refl refl refl bottom-left refl H =
    inv (right-unit ∙ right-unit ∙ H)

  reflect-top-right-coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) →
    coherence-pentagon-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( bottom-left)
      ( bottom-right) →
    coherence-pentagon-identifications
      ( inv bottom-right)
      ( inv bottom-left)
      ( inv top-right)
      ( inv top-left)
      ( inv top)
  reflect-top-right-coherence-pentagon-identifications
    refl top-left refl refl refl H =
    ap inv (inv right-unit ∙ H)

  reflect-bottom-left-coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) →
    coherence-pentagon-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( bottom-left)
      ( bottom-right) →
    coherence-pentagon-identifications
      ( inv top-right)
      ( bottom-right)
      ( inv top)
      ( inv bottom-left)
      ( top-left)
  reflect-bottom-left-coherence-pentagon-identifications
    refl refl refl refl bottom-right H = right-unit ∙ inv H

  reflect-bottom-right-coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) →
    coherence-pentagon-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( bottom-left)
      ( bottom-right) →
    coherence-pentagon-identifications
      ( bottom-left)
      ( inv top-left)
      ( inv bottom-right)
      ( top)
      ( inv top-right)
  reflect-bottom-right-coherence-pentagon-identifications
    refl refl refl bottom-left refl H =
    inv (right-unit ∙ right-unit ∙ H)
```
