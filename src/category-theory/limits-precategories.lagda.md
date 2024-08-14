# Limits in precategories

```agda
module category-theory.limits-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategories
open import category-theory.functors-precategories
open import category-theory.precategories
open import category-theory.right-extensions-precategories
open import category-theory.right-kan-extensions-precategories
open import category-theory.terminal-category
open import category-theory.terminal-objects-precategories

open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="of a functor of precategories" Agda=limit-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F` of
[precategories](category-theory.precategories.md) is the
[right kan extension](category-theory.right-kan-extensions-precategories.md) of
`F` along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

If a limit exists, we call the image of `star` under the extension the
**vertex** of the limit.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  limit-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  limit-Precategory =
    right-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D) (L : limit-Precategory C D F)
  where

  right-extension-limit-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  right-extension-limit-Precategory =
    right-extension-right-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L

  extension-limit-Precategory :
    functor-Precategory terminal-Precategory D
  extension-limit-Precategory =
    extension-right-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L

  vertex-limit-Precategory :
    obj-Precategory D
  vertex-limit-Precategory =
    obj-functor-Precategory terminal-Precategory D
      extension-limit-Precategory star
```
