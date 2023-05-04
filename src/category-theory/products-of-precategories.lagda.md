# Products of precategories

```agda
module category-theory.products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.sets
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.equality-cartesian-product-types
```

</details>

## Idea

The product of two precategories `C` and `D` has as objects pairs `(x , y)`, for `x` in `obj-Precat C` and `y` in `obj-Precat D`;
and has a morphism `Hom (x , y) (x' , y)` for each pair of morphisms `f : x → x'` and `g : y → y'`.
Composition of morphisms is given by composing each entry.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  where

  prod-Precat :
    Precat (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 prod-Precat = obj-Precat C × obj-Precat D
  pr1 (pr2 prod-Precat) (x , y) (x' , y') =
    prod-Set (hom-Precat C x x') (hom-Precat D y y')
  pr1 (pr1 (pr1 (pr2 (pr2 prod-Precat))) (f' , g') (f , g)) =
    comp-hom-Precat C f' f
  pr2 (pr1 (pr1 (pr2 (pr2 prod-Precat))) (f' , g') (f , g)) =
    comp-hom-Precat D g' g
  pr2 (pr1 (pr2 (pr2 prod-Precat))) (f'' , g'') (f' , g') (f , g) =
    eq-pair
      ( associative-comp-hom-Precat C f'' f' f)
      ( associative-comp-hom-Precat D g'' g' g)
  pr1 (pr1 (pr2 (pr2 (pr2 prod-Precat))) (x , y)) =
    id-hom-Precat C {x}
  pr2 (pr1 (pr2 (pr2 (pr2 prod-Precat))) (x , y)) =
    id-hom-Precat D {y}
  pr1 (pr2 (pr2 (pr2 (pr2 prod-Precat)))) (f , g) =
    eq-pair
      ( left-unit-law-comp-hom-Precat C f)
      ( left-unit-law-comp-hom-Precat D g)
  pr2 (pr2 (pr2 (pr2 (pr2 prod-Precat)))) (f , g) =
    eq-pair
      ( right-unit-law-comp-hom-Precat C f)
      ( right-unit-law-comp-hom-Precat D g)
```
