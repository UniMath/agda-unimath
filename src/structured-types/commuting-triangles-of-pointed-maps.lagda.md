# Commuting triangles of pointed maps

```agda
module structured-types.commuting-triangles-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition
```

</details>

## Idea

Consider a triangle of [pointed maps](structured-types.pointed-maps.md)

```text
           top
       A ──────> B
        ╲       ╱
    left ╲     ╱ right
          ╲   ╱
           ∨ ∨
            C
```

Such a triangle is said to be a
{{#concept "commuting triangle of pointed maps" Agda=coherence-triangle-pointed-maps}}
if there is a [pointed homotopy](structured-types.pointed-homotopies.md)

```text
  left ~∗ right ∘∗ top.
```

Such a homotopy is referred to as the
{{#concept "coherence" Disambiguation="commuting triangles of pointed maps" Agda=coherence-triangle-pointed-maps}}
of the commuting triangle of pointed maps.

## Definitions

### Coherences of commuting triangles of pointed maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (left : A →∗ C) (right : B →∗ C) (top : A →∗ B)
  where

  coherence-triangle-pointed-maps : UU (l1 ⊔ l3)
  coherence-triangle-pointed-maps =
    left ~∗ right ∘∗ top

  coherence-triangle-pointed-maps' : UU (l1 ⊔ l3)
  coherence-triangle-pointed-maps' =
    right ∘∗ top ~∗ left
```

## Properties

### Left whiskering of coherences of commuting triangles of pointed maps

Consider a commuting triangle of pointed maps

```text
           top
       A ──────> B
        ╲       ╱
    left ╲     ╱ right
          ╲   ╱
           ∨ ∨
            C
```

and consider a pointed map `f : C →∗ X`. The
{{#concept "left whiskering" Disambiguation="commuting triangles of pointed maps" Agda=left-whisker-coherence-triangle-pointed-maps}}
is a coherence of the triangle of pointed maps

```text
              top
          A ──────> B
           ╲       ╱
  f ∘∗ left ╲     ╱ f ∘∗ right
             ╲   ╱
              ∨ ∨
               X
```

In other words, left whiskering of coherences of commuting triangles of pointed
maps is an operation

```text
  (left ~∗ right ∘∗ top) → (f ∘∗ left ~∗ (f ∘∗ right) ∘∗ top).
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  {X : Pointed-Type l4} (f : C →∗ X)
  (left : A →∗ C) (right : B →∗ C) (top : A →∗ B)
  where

  left-whisker-coherence-triangle-pointed-maps :
    coherence-triangle-pointed-maps left right top →
    coherence-triangle-pointed-maps (f ∘∗ left) (f ∘∗ right) top
  left-whisker-coherence-triangle-pointed-maps H =
    concat-pointed-htpy
      ( left-whisker-comp-pointed-htpy f left (right ∘∗ top) H)
      ( inv-pointed-htpy
        ( associative-comp-pointed-map f right top))
```
