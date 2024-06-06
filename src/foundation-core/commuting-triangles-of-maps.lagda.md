# Commuting triangles of maps

```agda
module foundation-core.commuting-triangles-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A triangle of maps

```text
        top
     A ────> B
      ╲     ╱
  left ╲   ╱ right
        ∨ ∨
         X
```

is said to **commute** if there is a [homotopy](foundation-core.homotopies.md)
between the map on the left and the composite of the top and right maps:

```text
  left ~ right ∘ top.
```

## Definitions

### Commuting triangles of maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle-maps :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps left right top = left ~ right ∘ top

  coherence-triangle-maps' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps' left right top = right ∘ top ~ left
```

### Concatenation of commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) (i : A → B) (j : B → C)
  where

  concat-coherence-triangle-maps :
    coherence-triangle-maps f g i →
    coherence-triangle-maps g h j →
    coherence-triangle-maps f h (j ∘ i)
  concat-coherence-triangle-maps H K =
    H ∙h (K ·r i)
```

## Properties

### If the top map has a section, then the reversed triangle with the section on top commutes

If `t : B → A` is a [section](foundation-core.sections.md) of the top map `h`,
then the triangle

```text
       t
  B ──────> A
   ╲       ╱
   g╲     ╱f
     ╲   ╱
      ∨ ∨
       X
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (t : section h)
  where

  inv-triangle-section : coherence-triangle-maps' g f (map-section h t)
  inv-triangle-section =
    (H ·r map-section h t) ∙h (g ·l is-section-map-section h t)

  triangle-section : coherence-triangle-maps g f (map-section h t)
  triangle-section = inv-htpy inv-triangle-section
```

### If the right map has a retraction, then the reversed triangle with the retraction on the right commutes

If `r : X → B` is a retraction of the right map `g` in a triangle `f ~ g ∘ h`,
then the triangle

```text
       f
  A ──────> X
   ╲       ╱
   h╲     ╱r
     ╲   ╱
      ∨ ∨
       B
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (r : retraction g)
  where

  inv-triangle-retraction : coherence-triangle-maps' h (map-retraction g r) f
  inv-triangle-retraction =
    (map-retraction g r ·l H) ∙h (is-retraction-map-retraction g r ·r h)

  triangle-retraction : coherence-triangle-maps h (map-retraction g r) f
  triangle-retraction = inv-htpy inv-triangle-retraction
```
