# Coslice precategories

```agda
module category-theory.coslice-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.slice-precategories

open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "coslice precategory" Agda=Coslice-Precategory}} of a
[precategory](category-theory.precategories.md) `C` under an object `X` of `C`
is the category of objects of `C` equipped with a morphism from `X`.

Equivalently, it is the opposite of the slice precategory of `Cᵒᵖ`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  Coslice-Precategory : Precategory (l1 ⊔ l2) l2
  Coslice-Precategory =
    opposite-Precategory (Slice-Precategory (opposite-Precategory C) X)
```

## Properties

### The coslice precategory has a forgetful functor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  forgetful-functor-Coslice-Precategory :
    functor-Precategory (Coslice-Precategory C X) C
  forgetful-functor-Coslice-Precategory =
    opposite-functor-Precategory
      ( Slice-Precategory (opposite-Precategory C) X)
      ( opposite-Precategory C)
      ( forgetful-functor-Slice-Precategory (opposite-Precategory C) X)
```
