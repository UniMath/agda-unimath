# Opposite precategories

```agda
module category-theory.opposite-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [precategory](category-theory.precategories.md), its **opposite
precategory** `Cᵒᵖ` is given by reversing every morphism.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  opposite-Precategory : Precategory l1 l2
  pr1 opposite-Precategory = obj-Precategory C
  pr1 (pr2 opposite-Precategory) x y = hom-set-Precategory C y x
  pr1 (pr1 (pr2 (pr2 opposite-Precategory))) f g = comp-hom-Precategory C g f
  pr2 (pr1 (pr2 (pr2 opposite-Precategory))) f g h =
    inv (associative-comp-hom-Precategory C h g f)
  pr1 (pr2 (pr2 (pr2 opposite-Precategory))) x = id-hom-Precategory C {x}
  pr1 (pr2 (pr2 (pr2 (pr2 opposite-Precategory)))) f =
    right-unit-law-comp-hom-Precategory C f
  pr2 (pr2 (pr2 (pr2 (pr2 opposite-Precategory)))) f =
    left-unit-law-comp-hom-Precategory C f
```
