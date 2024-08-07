# Limits in precategories

```agda
module category-theory.limits-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategories
open import category-theory.functors-precategories
open import category-theory.precategories
open import category-theory.terminal-objects-precategories

open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="of a functor of precategories" Agda=limit-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F` of
[precategories](category-theory.precategories.md) is the
[terminal](category-theory.terminal-objects-precategories.md)
[cone](category-theory.cones-precategories.md) to `F`.

Following the terminology for cones, we call the vertex of the terminal cone the
**vertex** of the limit.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  limit-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  limit-Precategory =
    terminal-obj-Precategory (cone-precategory-Precategory C D F)

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D) (L : limit-Precategory C D F)
  where

  cone-limit-Precategory : cone-Precategory C D F
  cone-limit-Precategory =
    obj-terminal-obj-Precategory (cone-precategory-Precategory C D F) L

  vertex-limit-Precategory : obj-Precategory D
  vertex-limit-Precategory =
    vertex-cone-Precategory C D F cone-limit-Precategory

  is-limiting-cone-Precategory :
    is-terminal-obj-Precategory
      ( cone-precategory-Precategory C D F)
      ( cone-limit-Precategory)
  is-limiting-cone-Precategory =
    is-terminal-obj-terminal-obj-Precategory
      ( cone-precategory-Precategory C D F)
      ( L)
```
