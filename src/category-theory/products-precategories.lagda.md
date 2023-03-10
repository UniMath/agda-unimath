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
- morphisms `proj₁ : hom p x` and `proj₂ : hom p y`
such that for every object `z` and morphisms `f : hom z x` and `g : hom z y` there exists a unique morphism `h : hom z p` such that
- `comp proj₁ h = f`
- `comp proj₂ h = g`.

We say that `C` has all binary products if there is a choice of a product for each pair of objects in `C`.

## Definition

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) where

  is-product :
    (x y p : obj-Precat C) →
    type-hom-Precat C p x →
    type-hom-Precat C p y →
    UU (l1 ⊔ l2)
  is-product x y p proj₁ proj₂ =
    (z : obj-Precat C)
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    (∃! (type-hom-Precat C z p) λ h →
        (comp-hom-Precat C proj₁ h ＝ f)
        × (comp-hom-Precat C proj₂ h ＝ g))

  product : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  product x y =
    Σ (obj-Precat C) λ p →
    Σ (type-hom-Precat C p x) λ proj₁ →
    Σ (type-hom-Precat C p y) λ proj₂ →
      is-product x y p proj₁ proj₂

  has-all-binary-products : UU (l1 ⊔ l2)
  has-all-binary-products = (x y : obj-Precat C) → product x y

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C) where

  object-product : obj-Precat C → obj-Precat C → obj-Precat C
  object-product x y = pr1 (t x y)

  proj₁-product : (x y : obj-Precat C) → type-hom-Precat C (object-product x y) x
  proj₁-product x y = pr1 (pr2 (t x y))

  proj₂-product : (x y : obj-Precat C) → type-hom-Precat C (object-product x y) y
  proj₂-product x y = pr1 (pr2 (pr2 (t x y)))

  module _ (x y z : obj-Precat C)
    (f : type-hom-Precat C z x)
    (g : type-hom-Precat C z y) where

    morphism-into-product : type-hom-Precat C z (object-product x y)
    morphism-into-product = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-comm-proj₁ :
      comp-hom-Precat C (proj₁-product x y) morphism-into-product ＝ f
    morphism-into-product-comm-proj₁ =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-comm-proj₂ :
      comp-hom-Precat C (proj₂-product x y) morphism-into-product ＝ g
    morphism-into-product-comm-proj₂ =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product :
      (h : type-hom-Precat C z (object-product x y)) →
      comp-hom-Precat C (proj₁-product x y) h ＝ f →
      comp-hom-Precat C (proj₂-product x y) h ＝ g →
      morphism-into-product ＝ h
    is-unique-morphism-into-product h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (x y p : obj-Precat C)
  (proj₁ : type-hom-Precat C p x)
  (proj₂ : type-hom-Precat C p y) where

  is-prop-is-product : is-prop (is-product C x y p proj₁ proj₂)
  is-prop-is-product =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-product-Prop : Prop (l1 ⊔ l2)
  pr1 is-product-Prop = is-product C x y p proj₁ proj₂
  pr2 is-product-Prop = is-prop-is-product
```

## Properties

### Products of morphisms

If `C` has all binary products then for any pair of morphisms `f : hom x₁ y₁` and `g : hom x₂ y₂` we can construct a morphism `f × g : hom (x₁ × x₂) (y₁ × y₂)`.

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C)
  {x₁ x₂ y₁ y₂ : obj-Precat C}
  (f : type-hom-Precat C x₁ y₁)
  (g : type-hom-Precat C x₂ y₂) where

  product-of-morphisms :
    type-hom-Precat C
      (object-product C t x₁ x₂)
      (object-product C t y₁ y₂)
  product-of-morphisms =
    morphism-into-product C t _ _ _
      (comp-hom-Precat C f (proj₁-product C t x₁ x₂))
      (comp-hom-Precat C g (proj₂-product C t x₁ x₂))
```
