# Products in precategories

```agda
module category-theory.products-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

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
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-product-Precat :
    (x y p : obj-Precat C) →
    type-hom-Precat C p x →
    type-hom-Precat C p y →
    UU (l1 ⊔ l2)
  is-product-Precat x y p l r =
    (z : obj-Precat C)
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    (∃! (type-hom-Precat C z p) λ h →
        (comp-hom-Precat C l h ＝ f) × (comp-hom-Precat C r h ＝ g))

  product-Precat : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  product-Precat x y =
    Σ (obj-Precat C) λ p →
    Σ (type-hom-Precat C p x) λ l →
    Σ (type-hom-Precat C p y) λ r →
      is-product-Precat x y p l r

  has-all-binary-products-Precat : UU (l1 ⊔ l2)
  has-all-binary-products-Precat = (x y : obj-Precat C) → product-Precat x y

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products-Precat C)
  where

  object-product-Precat : obj-Precat C → obj-Precat C → obj-Precat C
  object-product-Precat x y = pr1 (t x y)

  pr1-product-Precat :
    (x y : obj-Precat C) → type-hom-Precat C (object-product-Precat x y) x
  pr1-product-Precat x y = pr1 (pr2 (t x y))

  pr2-product-Precat :
    (x y : obj-Precat C) → type-hom-Precat C (object-product-Precat x y) y
  pr2-product-Precat x y = pr1 (pr2 (pr2 (t x y)))

  module _
    (x y z : obj-Precat C)
    (f : type-hom-Precat C z x)
    (g : type-hom-Precat C z y)
    where

    morphism-into-product-Precat :
      type-hom-Precat C z (object-product-Precat x y)
    morphism-into-product-Precat = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-Precat-comm-pr1 :
      comp-hom-Precat C
        ( pr1-product-Precat x y)
        ( morphism-into-product-Precat) ＝ f
    morphism-into-product-Precat-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-Precat-comm-pr2 :
      comp-hom-Precat C
        ( pr2-product-Precat x y)
        ( morphism-into-product-Precat) ＝ g
    morphism-into-product-Precat-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product-Precat :
      (h : type-hom-Precat C z (object-product-Precat x y)) →
      comp-hom-Precat C (pr1-product-Precat x y) h ＝ f →
      comp-hom-Precat C (pr2-product-Precat x y) h ＝ g →
      morphism-into-product-Precat ＝ h
    is-unique-morphism-into-product-Precat h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (x y p : obj-Precat C)
  (l : type-hom-Precat C p x)
  (r : type-hom-Precat C p y)
  where

  is-prop-is-product-Precat : is-prop (is-product-Precat C x y p l r)
  is-prop-is-product-Precat =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-product-Precat-Prop : Prop (l1 ⊔ l2)
  pr1 is-product-Precat-Prop = is-product-Precat C x y p l r
  pr2 is-product-Precat-Prop = is-prop-is-product-Precat
```

## Properties

### Products of morphisms

If `C` has all binary products then for any pair of morphisms `f : hom x₁ y₁`
and `g : hom x₂ y₂` we can construct a morphism
`f × g : hom (x₁ × x₂) (y₁ × y₂)`.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products-Precat C)
  {x₁ x₂ y₁ y₂ : obj-Precat C}
  (f : type-hom-Precat C x₁ y₁)
  (g : type-hom-Precat C x₂ y₂)
  where

  map-product-Precat :
    type-hom-Precat C
      (object-product-Precat C t x₁ x₂)
      (object-product-Precat C t y₁ y₂)
  map-product-Precat =
    morphism-into-product-Precat C t _ _ _
      (comp-hom-Precat C f (pr1-product-Precat C t x₁ x₂))
      (comp-hom-Precat C g (pr2-product-Precat C t x₁ x₂))
```
