# Products in precategories

```agda
module category-theory.products-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unique-existence
open import foundation.universe-levels
```

</details>

## Idea

A product of two objects `x` and `x` in a category `C` consists of:

- an object `p`
- morphisms `l : hom p x` and `r : hom p y` such that for every object `z` and
  morphisms `f : hom z x` and `g : hom z y` there exists a unique morphism
  `h : hom z p` such that
- `l ∘ h = f`
- `r ∘ h = g`.

We say that `C` has all binary products if there is a choice of a product for
each pair of objects in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-product-Precategory :
    (x y p : obj-Precategory C) →
    type-hom-Precategory C p x →
    type-hom-Precategory C p y →
    UU (l1 ⊔ l2)
  is-product-Precategory x y p l r =
    (z : obj-Precategory C)
    (f : type-hom-Precategory C z x) →
    (g : type-hom-Precategory C z y) →
    (∃! (type-hom-Precategory C z p) λ h →
        (comp-hom-Precategory C l h ＝ f) × (comp-hom-Precategory C r h ＝ g))

  product-Precategory : obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  product-Precategory x y =
    Σ (obj-Precategory C) λ p →
    Σ (type-hom-Precategory C p x) λ l →
    Σ (type-hom-Precategory C p y) λ r →
      is-product-Precategory x y p l r

  has-all-binary-products-Precategory : UU (l1 ⊔ l2)
  has-all-binary-products-Precategory =
    (x y : obj-Precategory C) → product-Precategory x y

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-binary-products-Precategory C)
  where

  object-product-Precategory :
    obj-Precategory C → obj-Precategory C → obj-Precategory C
  object-product-Precategory x y = pr1 (t x y)

  pr1-product-Precategory :
    (x y : obj-Precategory C) →
    type-hom-Precategory C (object-product-Precategory x y) x
  pr1-product-Precategory x y = pr1 (pr2 (t x y))

  pr2-product-Precategory :
    (x y : obj-Precategory C) →
    type-hom-Precategory C (object-product-Precategory x y) y
  pr2-product-Precategory x y = pr1 (pr2 (pr2 (t x y)))

  module _
    (x y z : obj-Precategory C)
    (f : type-hom-Precategory C z x)
    (g : type-hom-Precategory C z y)
    where

    morphism-into-product-Precategory :
      type-hom-Precategory C z (object-product-Precategory x y)
    morphism-into-product-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-Precategory-comm-pr1 :
      comp-hom-Precategory C
        ( pr1-product-Precategory x y)
        ( morphism-into-product-Precategory) ＝ f
    morphism-into-product-Precategory-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-Precategory-comm-pr2 :
      comp-hom-Precategory C
        ( pr2-product-Precategory x y)
        ( morphism-into-product-Precategory) ＝ g
    morphism-into-product-Precategory-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product-Precategory :
      (h : type-hom-Precategory C z (object-product-Precategory x y)) →
      comp-hom-Precategory C (pr1-product-Precategory x y) h ＝ f →
      comp-hom-Precategory C (pr2-product-Precategory x y) h ＝ g →
      morphism-into-product-Precategory ＝ h
    is-unique-morphism-into-product-Precategory h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y p : obj-Precategory C)
  (l : type-hom-Precategory C p x)
  (r : type-hom-Precategory C p y)
  where

  is-prop-is-product-Precategory : is-prop (is-product-Precategory C x y p l r)
  is-prop-is-product-Precategory =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-product-Precategory-Prop : Prop (l1 ⊔ l2)
  pr1 is-product-Precategory-Prop = is-product-Precategory C x y p l r
  pr2 is-product-Precategory-Prop = is-prop-is-product-Precategory
```

## Properties

### Products of morphisms

If `C` has all binary products then for any pair of morphisms `f : hom x₁ y₁`
and `g : hom x₂ y₂` we can construct a morphism
`f × g : hom (x₁ × x₂) (y₁ × y₂)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-binary-products-Precategory C)
  {x₁ x₂ y₁ y₂ : obj-Precategory C}
  (f : type-hom-Precategory C x₁ y₁)
  (g : type-hom-Precategory C x₂ y₂)
  where

  map-product-Precategory :
    type-hom-Precategory C
      (object-product-Precategory C t x₁ x₂)
      (object-product-Precategory C t y₁ y₂)
  map-product-Precategory =
    morphism-into-product-Precategory C t _ _ _
      (comp-hom-Precategory C f (pr1-product-Precategory C t x₁ x₂))
      (comp-hom-Precategory C g (pr2-product-Precategory C t x₁ x₂))
```
