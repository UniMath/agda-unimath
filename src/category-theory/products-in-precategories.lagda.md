# Products in precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.products-in-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories funext

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.iterated-dependent-product-types funext
open import foundation.propositions funext
open import foundation.telescopes
open import foundation.uniqueness-quantification funext
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

  is-product-obj-Precategory :
    (x y p : obj-Precategory C) →
    hom-Precategory C p x →
    hom-Precategory C p y →
    UU (l1 ⊔ l2)
  is-product-obj-Precategory x y p l r =
    (z : obj-Precategory C)
    (f : hom-Precategory C z x) →
    (g : hom-Precategory C z y) →
    ( uniquely-exists-structure
      ( hom-Precategory C z p)
      ( λ h →
        ( comp-hom-Precategory C l h ＝ f) ×
        ( comp-hom-Precategory C r h ＝ g)))

  product-obj-Precategory : obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
  product-obj-Precategory x y =
    Σ (obj-Precategory C) λ p →
    Σ (hom-Precategory C p x) λ l →
    Σ (hom-Precategory C p y) λ r →
      is-product-obj-Precategory x y p l r

  has-all-binary-products-Precategory : UU (l1 ⊔ l2)
  has-all-binary-products-Precategory =
    (x y : obj-Precategory C) → product-obj-Precategory x y

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-binary-products-Precategory C)
  where

  object-product-obj-Precategory :
    obj-Precategory C → obj-Precategory C → obj-Precategory C
  object-product-obj-Precategory x y = pr1 (t x y)

  pr1-product-obj-Precategory :
    (x y : obj-Precategory C) →
    hom-Precategory C (object-product-obj-Precategory x y) x
  pr1-product-obj-Precategory x y = pr1 (pr2 (t x y))

  pr2-product-obj-Precategory :
    (x y : obj-Precategory C) →
    hom-Precategory C (object-product-obj-Precategory x y) y
  pr2-product-obj-Precategory x y = pr1 (pr2 (pr2 (t x y)))

  module _
    (x y z : obj-Precategory C)
    (f : hom-Precategory C z x)
    (g : hom-Precategory C z y)
    where

    morphism-into-product-obj-Precategory :
      hom-Precategory C z (object-product-obj-Precategory x y)
    morphism-into-product-obj-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-obj-Precategory-comm-pr1 :
      comp-hom-Precategory C
        ( pr1-product-obj-Precategory x y)
        ( morphism-into-product-obj-Precategory) ＝ f
    morphism-into-product-obj-Precategory-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-obj-Precategory-comm-pr2 :
      comp-hom-Precategory C
        ( pr2-product-obj-Precategory x y)
        ( morphism-into-product-obj-Precategory) ＝ g
    morphism-into-product-obj-Precategory-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product-obj-Precategory :
      (h : hom-Precategory C z (object-product-obj-Precategory x y)) →
      comp-hom-Precategory C (pr1-product-obj-Precategory x y) h ＝ f →
      comp-hom-Precategory C (pr2-product-obj-Precategory x y) h ＝ g →
      morphism-into-product-obj-Precategory ＝ h
    is-unique-morphism-into-product-obj-Precategory h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y p : obj-Precategory C)
  (l : hom-Precategory C p x)
  (r : hom-Precategory C p y)
  where

  is-prop-is-product-obj-Precategory :
    is-prop (is-product-obj-Precategory C x y p l r)
  is-prop-is-product-obj-Precategory =
    is-prop-iterated-Π 3 (λ z f g → is-property-is-contr)

  is-product-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-product-prop-Precategory = is-product-obj-Precategory C x y p l r
  pr2 is-product-prop-Precategory = is-prop-is-product-obj-Precategory
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
  (f : hom-Precategory C x₁ y₁)
  (g : hom-Precategory C x₂ y₂)
  where

  map-product-obj-Precategory :
    hom-Precategory C
      (object-product-obj-Precategory C t x₁ x₂)
      (object-product-obj-Precategory C t y₁ y₂)
  map-product-obj-Precategory =
    morphism-into-product-obj-Precategory C t _ _ _
      (comp-hom-Precategory C f (pr1-product-obj-Precategory C t x₁ x₂))
      (comp-hom-Precategory C g (pr2-product-obj-Precategory C t x₁ x₂))
```
