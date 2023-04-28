# Exponential objects in precategories

```agda
module category-theory.exponential-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.products-precategories

open import foundation.dependent-pair-types
open import foundation.unique-existence
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Let `C` be a category with all binary products. For objects `x` and `y` in `C`,
an exponential (often denoted y^x) consists of:

- an object `e`
- a morphism `ev : hom (e × x) y` such that for every object `z` and morphism
  `f : hom (z × x) y` there exists a unique morphism `g : hom z e` such that
- `comp (g × id x) ev = f`.

We say that `C` has all exponentials if there is a choice of an exponential for
each pair of objects.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (p : has-all-binary-products-Precat C)
  where

  is-exponential-Precat :
    (x y e : obj-Precat C) →
    type-hom-Precat C (object-product-Precat C p e x) y →
    UU (l1 ⊔ l2)
  is-exponential-Precat x y e ev =
    (z : obj-Precat C)
    (f : type-hom-Precat C (object-product-Precat C p z x) y) →
    ∃! (type-hom-Precat C z e) λ g →
       comp-hom-Precat C ev (map-product-Precat C p g (id-hom-Precat C)) ＝ f

  exponential-Precat : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  exponential-Precat x y =
    Σ (obj-Precat C) (λ e →
    Σ (type-hom-Precat C (object-product-Precat C p e x) y) λ ev →
      is-exponential-Precat x y e ev)

  has-all-exponentials-Precat : UU (l1 ⊔ l2)
  has-all-exponentials-Precat = (x y : obj-Precat C) → exponential-Precat x y

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (p : has-all-binary-products-Precat C)
  (t : has-all-exponentials-Precat C p)
  (x y : obj-Precat C)
  where

  object-exponential-Precat : obj-Precat C
  object-exponential-Precat = pr1 (t x y)

  eval-exponential-Precat :
    type-hom-Precat C (object-product-Precat C p object-exponential-Precat x) y
  eval-exponential-Precat = pr1 (pr2 (t x y))

  module _
    (z : obj-Precat C)
    (f : type-hom-Precat C (object-product-Precat C p z x) y)
    where

    morphism-into-exponential-Precat :
      type-hom-Precat C z object-exponential-Precat
    morphism-into-exponential-Precat = pr1 (pr1 (pr2 (pr2 (t x y)) z f))

    morphism-into-exponential-Precat-comm :
      comp-hom-Precat C
          ( eval-exponential-Precat)
          ( map-product-Precat C p
            (morphism-into-exponential-Precat)
            (id-hom-Precat C)) ＝ f
    morphism-into-exponential-Precat-comm = pr2 (pr1 (pr2 (pr2 (t x y)) z f))

    is-unique-morphism-into-exponential-Precat :
      ( g : type-hom-Precat C z object-exponential-Precat) →
      ( comp-hom-Precat C
        ( eval-exponential-Precat)
        ( map-product-Precat C p g (id-hom-Precat C)) ＝ f) →
      morphism-into-exponential-Precat ＝ g
    is-unique-morphism-into-exponential-Precat g q =
      ap pr1 (pr2 (pr2 (pr2 (t x y)) z f) (g , q))
```
