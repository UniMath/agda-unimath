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

We manually dualize the definition of products in precategories for convenience. See
the documentation in that file for further information.

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) where

  is-coproduct :
    (x y p : obj-Precat C) →
    type-hom-Precat C x p → type-hom-Precat C y p → UU (l1 ⊔ l2)
  is-coproduct x y p inj₁ inj₂ =
    (z : obj-Precat C)
    (f : type-hom-Precat C x z) →
    (g : type-hom-Precat C y z) →
    (∃! ( type-hom-Precat C p z)
        ( λ h →
          ( comp-hom-Precat C h inj₁ ＝ f) × (comp-hom-Precat C h inj₂ ＝ g)))

  coproduct : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  coproduct x y =
    Σ ( obj-Precat C)
      ( λ p →
        Σ ( type-hom-Precat C x p)
          ( λ inj₁ →
            Σ (type-hom-Precat C y p)
              ( λ inj₂ →
                  is-coproduct x y p inj₁ inj₂)))

  has-all-binary-coproducts : UU (l1 ⊔ l2)
  has-all-binary-coproducts = (x y : obj-Precat C) → coproduct x y

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-coproducts C) where

  object-coproduct : obj-Precat C → obj-Precat C → obj-Precat C
  object-coproduct x y = pr1 (t x y)

  inj₁-coproduct :
    (x y : obj-Precat C) → type-hom-Precat C x (object-coproduct x y)
  inj₁-coproduct x y = pr1 (pr2 (t x y))

  inj₂-coproduct :
    (x y : obj-Precat C) → type-hom-Precat C y (object-coproduct x y)
  inj₂-coproduct x y = pr1 (pr2 (pr2 (t x y)))

  module _ (x y z : obj-Precat C)
    (f : type-hom-Precat C x z)
    (g : type-hom-Precat C y z) where

    morphism-out-of-coproduct : type-hom-Precat C (object-coproduct x y) z
    morphism-out-of-coproduct = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-out-of-coproduct-comm-inj₁ :
      comp-hom-Precat C morphism-out-of-coproduct (inj₁-coproduct x y) ＝ f
    morphism-out-of-coproduct-comm-inj₁ =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-out-of-coproduct-comm-inj₂ :
      comp-hom-Precat C morphism-out-of-coproduct (inj₂-coproduct x y) ＝ g
    morphism-out-of-coproduct-comm-inj₂ =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-out-of-coproduct :
      (h : type-hom-Precat C (object-coproduct x y) z) →
      comp-hom-Precat C h (inj₁-coproduct x y) ＝ f →
      comp-hom-Precat C h (inj₂-coproduct x y) ＝ g →
      morphism-out-of-coproduct ＝ h
    is-unique-morphism-out-of-coproduct h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (x y p : obj-Precat C)
  (inj₁ : type-hom-Precat C x p)
  (inj₂ : type-hom-Precat C y p) where

  is-prop-is-coproduct : is-prop (is-coproduct C x y p inj₁ inj₂)
  is-prop-is-coproduct =
    is-prop-Π (λ z →
      is-prop-Π (λ f →
        is-prop-Π (λ g →
          is-property-is-contr)))

  is-coproduct-Prop : Prop (l1 ⊔ l2)
  pr1 is-coproduct-Prop = is-coproduct C x y p inj₁ inj₂
  pr2 is-coproduct-Prop = is-prop-is-coproduct
```

## Properties

### Coproducts of morphisms

If `C` has all binary coproducts then for any pair of morphisms `f : hom x₁ y₁` and `g : hom x₂ y₂` we can construct a morphism `f + g : hom (x₁ + x₂) (y₁ + y₂)`.

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-coproducts C)
  {x₁ x₂ y₁ y₂ : obj-Precat C}
  (f : type-hom-Precat C x₁ y₁)
  (g : type-hom-Precat C x₂ y₂) where

  coproduct-of-morphisms :
    type-hom-Precat C
      (object-coproduct C t x₁ x₂)
      (object-coproduct C t y₁ y₂)
  coproduct-of-morphisms =
    morphism-out-of-coproduct C t _ _ _
      (comp-hom-Precat C (inj₁-coproduct C t y₁ y₂) f)
      (comp-hom-Precat C (inj₂-coproduct C t y₁ y₂) g)
```
