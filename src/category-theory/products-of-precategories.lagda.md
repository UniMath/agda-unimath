# Products of precategories

```agda
module category-theory.products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The **product** of two [precategories](category-theory.precategories.md) `C` and
`D` has as objects pairs `(x , y)`, for `x` in `obj-Precategory C` and `y` in
`obj-Precategory D`; and has a morphism `Hom (x , y) (x' , y)` for each pair of
morphisms `f : x → x'` and `g : y → y'`. Composition of morphisms is given by
composing each entry.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  prod-Precategory :
    Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 prod-Precategory = obj-Precategory C × obj-Precategory D
  pr1 (pr2 prod-Precategory) (x , y) (x' , y') =
    prod-Set (hom-Precategory C x x') (hom-Precategory D y y')
  pr1 (pr1 (pr1 (pr2 (pr2 prod-Precategory))) (f' , g') (f , g)) =
    comp-hom-Precategory C f' f
  pr2 (pr1 (pr1 (pr2 (pr2 prod-Precategory))) (f' , g') (f , g)) =
    comp-hom-Precategory D g' g
  pr2 (pr1 (pr2 (pr2 prod-Precategory))) (f'' , g'') (f' , g') (f , g) =
    eq-pair
      ( associative-comp-hom-Precategory C f'' f' f)
      ( associative-comp-hom-Precategory D g'' g' g)
  pr1 (pr1 (pr2 (pr2 (pr2 prod-Precategory))) (x , y)) =
    id-hom-Precategory C {x}
  pr2 (pr1 (pr2 (pr2 (pr2 prod-Precategory))) (x , y)) =
    id-hom-Precategory D {y}
  pr1 (pr2 (pr2 (pr2 (pr2 prod-Precategory)))) (f , g) =
    eq-pair
      ( left-unit-law-comp-hom-Precategory C f)
      ( left-unit-law-comp-hom-Precategory D g)
  pr2 (pr2 (pr2 (pr2 (pr2 prod-Precategory)))) (f , g) =
    eq-pair
      ( right-unit-law-comp-hom-Precategory C f)
      ( right-unit-law-comp-hom-Precategory D g)
```
