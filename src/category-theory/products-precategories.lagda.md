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
- morphisms `pr1 : hom p x` and `pr2 : hom p y` such that for every object `z`
  and morphisms `f : hom z x` and `g : hom z y` there exists a unique morphism
  `h : hom z p` such that
- `comp pr1 h = f`
- `comp pr2 h = g`.

We say that `C` has all binary products if there is a choice of a product for
each pair of objects in `C`.

## Definition

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) where

  is-product :
    (x y p : obj-Precat C) →
    type-hom-Precat C p x →
    type-hom-Precat C p y →
    UU (l1 ⊔ l2)
  is-product x y p pr1 pr2 =
    (z : obj-Precat C)
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    (∃! (type-hom-Precat C z p) λ h →
        (comp-hom-Precat C pr1 h ＝ f)
        × (comp-hom-Precat C pr2 h ＝ g))

  product : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  product x y =
    Σ (obj-Precat C) λ p →
    Σ (type-hom-Precat C p x) λ pr1 →
    Σ (type-hom-Precat C p y) λ pr2 →
      is-product x y p pr1 pr2

  has-all-binary-products : UU (l1 ⊔ l2)
  has-all-binary-products = (x y : obj-Precat C) → product x y

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C) where

  object-product : obj-Precat C → obj-Precat C → obj-Precat C
  object-product x y = pr1 (t x y)

  pr1-product : (x y : obj-Precat C) → type-hom-Precat C (object-product x y) x
  pr1-product x y = pr1 (pr2 (t x y))

  pr2-product : (x y : obj-Precat C) → type-hom-Precat C (object-product x y) y
  pr2-product x y = pr1 (pr2 (pr2 (t x y)))

  module _ (x y z : obj-Precat C)
    (f : type-hom-Precat C z x)
    (g : type-hom-Precat C z y) where

    morphism-into-product : type-hom-Precat C z (object-product x y)
    morphism-into-product = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-comm-pr1 :
      comp-hom-Precat C (pr1-product x y) morphism-into-product ＝ f
    morphism-into-product-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-comm-pr2 :
      comp-hom-Precat C (pr2-product x y) morphism-into-product ＝ g
    morphism-into-product-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product :
      (h : type-hom-Precat C z (object-product x y)) →
      comp-hom-Precat C (pr1-product x y) h ＝ f →
      comp-hom-Precat C (pr2-product x y) h ＝ g →
      morphism-into-product ＝ h
    is-unique-morphism-into-product h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (x y p : obj-Precat C)
  (pr1 : type-hom-Precat C p x)
  (pr2 : type-hom-Precat C p y) where

  is-prop-is-product : is-prop (is-product C x y p pr1 pr2)
  is-prop-is-product =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-product-Prop : Prop (l1 ⊔ l2)
  pr1 is-product-Prop = is-product C x y p pr1 pr2
  pr2 is-product-Prop = is-prop-is-product
```

## Properties

### Products of morphisms

If `C` has all binary products then for any pair of morphisms `f : hom x₁ y₁`
and `g : hom x₂ y₂` we can construct a morphism
`f × g : hom (x₁ × x₂) (y₁ × y₂)`.

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
      (comp-hom-Precat C f (pr1-product C t x₁ x₂))
      (comp-hom-Precat C g (pr2-product C t x₁ x₂))
```
