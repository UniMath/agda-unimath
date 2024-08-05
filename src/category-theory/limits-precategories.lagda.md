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

The limit of a functor `F in a precategory is the terminal cone to `F`.

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

  is-limiting-cone :
    is-terminal-obj-Precategory
      ( cone-precategory-Precategory C D F)
      ( cone-limit-Precategory)
  is-limiting-cone =
    is-terminal-obj-terminal-obj-Precategory
      ( cone-precategory-Precategory C D F)
      ( L)
```
