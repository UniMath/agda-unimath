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
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of precategories" Agda=product-Precategory}}
of two [precategories](category-theory.precategories.md) `C` and `D` has as
objects [pairs](foundation-core.cartesian-product-types.md) `(x , y)`, where `x`
is an object of `C` and `y` is an object of `D`, and has as morphisms from
`(x , y)` to `(x' , y)` pairs `(f , g)` where `f : x → x'` in `C` and
`g : y → y'` in `D`. Composition of morphisms is given componentwise.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  obj-product-Precategory : UU (l1 ⊔ l3)
  obj-product-Precategory = obj-Precategory C × obj-Precategory D

  hom-set-product-Precategory :
    obj-product-Precategory → obj-product-Precategory → Set (l2 ⊔ l4)
  hom-set-product-Precategory (x , y) (x' , y') =
    product-Set (hom-set-Precategory C x x') (hom-set-Precategory D y y')

  hom-product-Precategory :
    obj-product-Precategory → obj-product-Precategory → UU (l2 ⊔ l4)
  hom-product-Precategory p q = type-Set (hom-set-product-Precategory p q)

  is-set-hom-product-Precategory :
    (p q : obj-product-Precategory) → is-set (hom-product-Precategory p q)
  is-set-hom-product-Precategory p q =
    is-set-type-Set (hom-set-product-Precategory p q)

  comp-hom-product-Precategory :
    {p q r : obj-product-Precategory}
    (g : hom-product-Precategory q r)
    (f : hom-product-Precategory p q) →
    hom-product-Precategory p r
  comp-hom-product-Precategory (f' , g') (f , g) =
    ( comp-hom-Precategory C f' f , comp-hom-Precategory D g' g)

  id-hom-product-Precategory :
    {p : obj-product-Precategory} → hom-product-Precategory p p
  id-hom-product-Precategory = id-hom-Precategory C , id-hom-Precategory D

  associative-comp-hom-product-Precategory :
    {p q r s : obj-product-Precategory}
    (h : hom-product-Precategory r s)
    (g : hom-product-Precategory q r)
    (f : hom-product-Precategory p q) →
    comp-hom-product-Precategory (comp-hom-product-Precategory h g) f ＝
    comp-hom-product-Precategory h (comp-hom-product-Precategory g f)
  associative-comp-hom-product-Precategory (f'' , g'') (f' , g') (f , g) =
    eq-pair
      ( associative-comp-hom-Precategory C f'' f' f)
      ( associative-comp-hom-Precategory D g'' g' g)

  left-unit-law-comp-hom-product-Precategory :
    {p q : obj-product-Precategory}
    (f : hom-product-Precategory p q) →
    comp-hom-product-Precategory id-hom-product-Precategory f ＝ f
  left-unit-law-comp-hom-product-Precategory (f , g) =
    eq-pair
      ( left-unit-law-comp-hom-Precategory C f)
      ( left-unit-law-comp-hom-Precategory D g)

  right-unit-law-comp-hom-product-Precategory :
    {p q : obj-product-Precategory}
    (f : hom-product-Precategory p q) →
    comp-hom-product-Precategory f id-hom-product-Precategory ＝ f
  right-unit-law-comp-hom-product-Precategory (f , g) =
    eq-pair
      ( right-unit-law-comp-hom-Precategory C f)
      ( right-unit-law-comp-hom-Precategory D g)

  product-Precategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  product-Precategory =
    make-Precategory
      ( obj-product-Precategory)
      ( hom-set-product-Precategory)
      ( comp-hom-product-Precategory)
      ( λ x → id-hom-product-Precategory {x})
      ( associative-comp-hom-product-Precategory)
      ( left-unit-law-comp-hom-product-Precategory)
      ( right-unit-law-comp-hom-product-Precategory)
```
