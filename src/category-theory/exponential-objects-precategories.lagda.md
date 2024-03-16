# Exponential objects in precategories

```agda
module category-theory.exponential-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.products-in-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.uniqueness-quantification
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a category with all binary products. For objects `x` and `y` in `C`,
an exponential (often denoted y^x) consists of:

- an object `e`
- a morphism `ev : hom (e × x) y` such that for every object `z` and morphism
  `f : hom (z × x) y` there exists a unique morphism `g : hom z e` such that
- `(g × id x) ∘ ev = f`.

We say that `C` has all exponentials if there is a choice of an exponential for
each pair of objects.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (p : has-all-binary-products-Precategory C)
  where

  is-exponential-obj-Precategory :
    (x y e : obj-Precategory C) →
    hom-Precategory C (object-product-obj-Precategory C p e x) y →
    UU (l1 ⊔ l2)
  is-exponential-obj-Precategory x y e ev =
    (z : obj-Precategory C)
    (f : hom-Precategory C (object-product-obj-Precategory C p z x) y) →
    uniquely-exists-structure
      ( hom-Precategory C z e)
      ( λ g →
        comp-hom-Precategory C ev
          ( map-product-obj-Precategory C p g (id-hom-Precategory C)) ＝
          ( f))

  exponential-obj-Precategory :
    obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  exponential-obj-Precategory x y =
    Σ (obj-Precategory C) (λ e →
    Σ (hom-Precategory C (object-product-obj-Precategory C p e x) y) λ ev →
      is-exponential-obj-Precategory x y e ev)

  has-all-exponentials-Precategory : UU (l1 ⊔ l2)
  has-all-exponentials-Precategory =
    (x y : obj-Precategory C) → exponential-obj-Precategory x y

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (p : has-all-binary-products-Precategory C)
  (t : has-all-exponentials-Precategory C p)
  (x y : obj-Precategory C)
  where

  object-exponential-obj-Precategory : obj-Precategory C
  object-exponential-obj-Precategory = pr1 (t x y)

  eval-exponential-obj-Precategory :
    hom-Precategory C
      ( object-product-obj-Precategory C p object-exponential-obj-Precategory x)
      ( y)
  eval-exponential-obj-Precategory = pr1 (pr2 (t x y))

  module _
    (z : obj-Precategory C)
    (f : hom-Precategory C (object-product-obj-Precategory C p z x) y)
    where

    morphism-into-exponential-obj-Precategory :
      hom-Precategory C z object-exponential-obj-Precategory
    morphism-into-exponential-obj-Precategory =
      pr1 (pr1 (pr2 (pr2 (t x y)) z f))

    morphism-into-exponential-obj-Precategory-comm :
      ( comp-hom-Precategory C
        ( eval-exponential-obj-Precategory)
        ( map-product-obj-Precategory C p
          ( morphism-into-exponential-obj-Precategory)
          ( id-hom-Precategory C))) ＝
      ( f)
    morphism-into-exponential-obj-Precategory-comm =
      pr2 (pr1 (pr2 (pr2 (t x y)) z f))

    is-unique-morphism-into-exponential-obj-Precategory :
      ( g : hom-Precategory C z object-exponential-obj-Precategory) →
      ( comp-hom-Precategory C
        ( eval-exponential-obj-Precategory)
        ( map-product-obj-Precategory C p g (id-hom-Precategory C)) ＝ f) →
      morphism-into-exponential-obj-Precategory ＝ g
    is-unique-morphism-into-exponential-obj-Precategory g q =
      ap pr1 (pr2 (pr2 (pr2 (t x y)) z f) (g , q))
```
