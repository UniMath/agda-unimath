# Reduced coslice precategories

```agda
module category-theory.reduced-coslice-precategory where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coslice-precategories
open import category-theory.full-subprecategories
open import category-theory.functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "reduced coslice precategory" Agda=Reduced-Coslice-Precategory}}
of a [precategory](category-theory.precategories.md) `C` under an object `X` of
`C` is the category of objects of `C` equipped with a non-identity morphism from
`X`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  Reduced-Coslice-Full-Subprecategory :
    Full-Subprecategory (l1 ⊔ l2) (Coslice-Precategory C X)
  pr1 (Reduced-Coslice-Full-Subprecategory (Y,f)) =
    ¬ ((Y,f) ＝ ((X , id-hom-Precategory C)))
  pr2 (Reduced-Coslice-Full-Subprecategory (Y,f)) =
    is-prop-neg

  Reduced-Coslice-Precategory : Precategory (l1 ⊔ l2) l2
  Reduced-Coslice-Precategory =
    precategory-Full-Subprecategory (Coslice-Precategory C X)
      Reduced-Coslice-Full-Subprecategory
```

## Properties

### The inclusion functor into the coslice precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  inclusion-coslice-Reduced-Coslice-Precategory :
    functor-Precategory
      ( Reduced-Coslice-Precategory C X)
      ( Coslice-Precategory C X)
  inclusion-coslice-Reduced-Coslice-Precategory =
    inclusion-Full-Subprecategory
      ( Coslice-Precategory C X)
      ( Reduced-Coslice-Full-Subprecategory C X)
```

### The reduced coslice precategory has a forgetful functor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  forgetful-functor-Reduced-Coslice-Precategory :
    functor-Precategory (Reduced-Coslice-Precategory C X) C
  forgetful-functor-Reduced-Coslice-Precategory =
    comp-functor-Precategory
      ( Reduced-Coslice-Precategory C X)
      ( Coslice-Precategory C X)
      ( C)
      ( forgetful-functor-Coslice-Precategory C X)
      ( inclusion-coslice-Reduced-Coslice-Precategory C X)
```
