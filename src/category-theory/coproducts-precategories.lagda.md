# Coproducts in precategories

```agda
module category-theory.coproducts-precategories where
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

We manually dualize the definition of products in precategories for convenience.
See the documentation in that file for further information.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-coproduct-Precat :
    (x y p : obj-Precat C) →
    type-hom-Precat C x p → type-hom-Precat C y p → UU (l1 ⊔ l2)
  is-coproduct-Precat x y p l r =
    (z : obj-Precat C)
    (f : type-hom-Precat C x z) →
    (g : type-hom-Precat C y z) →
    (∃! ( type-hom-Precat C p z)
        ( λ h → (comp-hom-Precat C h l ＝ f) × (comp-hom-Precat C h r ＝ g)))

  coproduct-Precat : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  coproduct-Precat x y =
    Σ ( obj-Precat C)
      ( λ p →
        Σ ( type-hom-Precat C x p)
          ( λ l →
            Σ (type-hom-Precat C y p)
              ( is-coproduct-Precat x y p l)))

  has-all-binary-coproducts : UU (l1 ⊔ l2)
  has-all-binary-coproducts = (x y : obj-Precat C) → coproduct-Precat x y

module _
  {l1 l2 : Level} (C : Precat l1 l2) (t : has-all-binary-coproducts C)
  where

  object-coproduct-Precat : obj-Precat C → obj-Precat C → obj-Precat C
  object-coproduct-Precat x y = pr1 (t x y)

  inl-coproduct-Precat :
    (x y : obj-Precat C) → type-hom-Precat C x (object-coproduct-Precat x y)
  inl-coproduct-Precat x y = pr1 (pr2 (t x y))

  inr-coproduct-Precat :
    (x y : obj-Precat C) → type-hom-Precat C y (object-coproduct-Precat x y)
  inr-coproduct-Precat x y = pr1 (pr2 (pr2 (t x y)))

  module _
    (x y z : obj-Precat C)
    (f : type-hom-Precat C x z)
    (g : type-hom-Precat C y z)
    where

    morphism-out-of-coproduct-Precat :
      type-hom-Precat C (object-coproduct-Precat x y) z
    morphism-out-of-coproduct-Precat = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-out-of-coproduct-Precat-comm-inl :
      comp-hom-Precat
        ( C)
        ( morphism-out-of-coproduct-Precat)
        ( inl-coproduct-Precat x y) ＝ f
    morphism-out-of-coproduct-Precat-comm-inl =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-out-of-coproduct-Precat-comm-inr :
      comp-hom-Precat
        ( C)
        ( morphism-out-of-coproduct-Precat)
        ( inr-coproduct-Precat x y) ＝ g
    morphism-out-of-coproduct-Precat-comm-inr =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-out-of-coproduct-Precat :
      (h : type-hom-Precat C (object-coproduct-Precat x y) z) →
      comp-hom-Precat C h (inl-coproduct-Precat x y) ＝ f →
      comp-hom-Precat C h (inr-coproduct-Precat x y) ＝ g →
      morphism-out-of-coproduct-Precat ＝ h
    is-unique-morphism-out-of-coproduct-Precat h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (x y p : obj-Precat C)
  (l : type-hom-Precat C x p)
  (r : type-hom-Precat C y p)
  where

  is-prop-is-coproduct-Precat : is-prop (is-coproduct-Precat C x y p l r)
  is-prop-is-coproduct-Precat =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-coproduct-Precat-Prop : Prop (l1 ⊔ l2)
  pr1 is-coproduct-Precat-Prop = is-coproduct-Precat C x y p l r
  pr2 is-coproduct-Precat-Prop = is-prop-is-coproduct-Precat
```

## Properties

### Coproducts of morphisms

If `C` has all binary coproducts then for any pair of morphisms `f : hom x₁ y₁`
and `g : hom x₂ y₂` we can construct a morphism
`f + g : hom (x₁ + x₂) (y₁ + y₂)`.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-coproducts C)
  {x₁ x₂ y₁ y₂ : obj-Precat C}
  (f : type-hom-Precat C x₁ y₁)
  (g : type-hom-Precat C x₂ y₂)
  where

  map-coproduct-Precat :
    type-hom-Precat C
      (object-coproduct-Precat C t x₁ x₂)
      (object-coproduct-Precat C t y₁ y₂)
  map-coproduct-Precat =
    morphism-out-of-coproduct-Precat C t _ _ _
      (comp-hom-Precat C (inl-coproduct-Precat C t y₁ y₂) f)
      (comp-hom-Precat C (inr-coproduct-Precat C t y₁ y₂) g)
```
