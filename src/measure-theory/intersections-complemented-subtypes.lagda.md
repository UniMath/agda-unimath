# Intersections of complemented subtypes

```agda
module measure-theory.intersections-complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import measure-theory.complemented-subtypes
```

</details>

## Idea

## Definition

### Intersection of two complemented subtypes

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l3)
  (cB@(B , B' , B#B') : complemented-subtype-Type-With-Apartness X l4)
  where

  subtype-intersection-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  subtype-intersection-complemented-subtype-Type-With-Apartness =
    intersection-subtype A B

  complement-subtype-intersection-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  complement-subtype-intersection-complemented-subtype-Type-With-Apartness =
    union-subtype
      ( intersection-subtype A' (union-subtype B B'))
      ( intersection-subtype A B')
```
