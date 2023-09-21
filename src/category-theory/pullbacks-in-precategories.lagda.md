# Pullbacks in precategories

```agda
module category-theory.pullbacks-in-precategories where
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

A pullback of two morphisms `f : hom y x` and `g : hom z x` in a category `C`
consists of:

- an object `w`
- morphisms `p₁ : hom w y` and `p₂ : hom w z` such that
- `f ∘ p₁ = g ∘ p₂` together with the universal property that for every object
  `w'` and pair of morphisms `p₁' : hom w' y` and `p₂' : hom w' z` such that
  `f ∘ p₁' = g ∘ p₂'` there exists a unique morphism `h : hom w' w` such that
- `p₁ ∘ h = p₁'`
- `p₂ ∘ h = p₂'`.

We say that `C` has all pullbacks if there is a choice of a pullback for each
object `x` and pair of morphisms into `x` in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pullback-Precategory :
    (x y z : obj-Precategory C) →
    (f : type-hom-Precategory C y x) →
    (g : type-hom-Precategory C z x) →
    (w : obj-Precategory C) →
    (p₁ : type-hom-Precategory C w y) →
    (p₂ : type-hom-Precategory C w z) →
    comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂ →
    UU (l1 ⊔ l2)
  is-pullback-Precategory x y z f g w p₁ p₂ _ =
    (w' : obj-Precategory C) →
    (p₁' : type-hom-Precategory C w' y) →
    (p₂' : type-hom-Precategory C w' z) →
    comp-hom-Precategory C f p₁' ＝ comp-hom-Precategory C g p₂' →
    ∃!
      ( type-hom-Precategory C w' w)
      ( λ h →
        ( comp-hom-Precategory C p₁ h ＝ p₁') ×
        ( comp-hom-Precategory C p₂ h ＝ p₂'))

  pullback-Precategory :
    (x y z : obj-Precategory C) →
    type-hom-Precategory C y x →
    type-hom-Precategory C z x →
    UU (l1 ⊔ l2)
  pullback-Precategory x y z f g =
    Σ (obj-Precategory C) λ w →
    Σ (type-hom-Precategory C w y) λ p₁ →
    Σ (type-hom-Precategory C w z) λ p₂ →
    Σ (comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂) λ α →
      is-pullback-Precategory x y z f g w p₁ p₂ α

  has-all-pullback-Precategory : UU (l1 ⊔ l2)
  has-all-pullback-Precategory =
    (x y z : obj-Precategory C) →
    (f : type-hom-Precategory C y x) →
    (g : type-hom-Precategory C z x) →
    pullback-Precategory x y z f g

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-pullback-Precategory C)
  (x y z : obj-Precategory C)
  (f : type-hom-Precategory C y x)
  (g : type-hom-Precategory C z x)
  where

  object-pullback-Precategory : obj-Precategory C
  object-pullback-Precategory = pr1 (t x y z f g)

  pr1-pullback-Precategory :
    type-hom-Precategory C object-pullback-Precategory y
  pr1-pullback-Precategory = pr1 (pr2 (t x y z f g))

  pr2-pullback-Precategory :
    type-hom-Precategory C object-pullback-Precategory z
  pr2-pullback-Precategory = pr1 (pr2 (pr2 (t x y z f g)))

  pullback-square-Precategory-comm :
    comp-hom-Precategory C f pr1-pullback-Precategory ＝
    comp-hom-Precategory C g pr2-pullback-Precategory
  pullback-square-Precategory-comm = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _
    (w' : obj-Precategory C)
    (p₁' : type-hom-Precategory C w' y)
    (p₂' : type-hom-Precategory C w' z)
    (α : comp-hom-Precategory C f p₁' ＝ comp-hom-Precategory C g p₂')
    where

    morphism-into-pullback-Precategory :
      type-hom-Precategory C w' object-pullback-Precategory
    morphism-into-pullback-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α))

    morphism-into-pullback-comm-pr1 :
      comp-hom-Precategory C
        pr1-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      p₁'
    morphism-into-pullback-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    morphism-into-pullback-comm-pr2 :
      comp-hom-Precategory C
        pr2-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      p₂'
    morphism-into-pullback-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    is-unique-morphism-into-pullback-Precategory :
      (h' : type-hom-Precategory C w' object-pullback-Precategory) →
      comp-hom-Precategory C pr1-pullback-Precategory h' ＝ p₁' →
      comp-hom-Precategory C pr2-pullback-Precategory h' ＝ p₂' →
      morphism-into-pullback-Precategory ＝ h'
    is-unique-morphism-into-pullback-Precategory h' α₁ α₂ =
      ap
        ( pr1)
        ( pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α) (h' , α₁ , α₂))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y z : obj-Precategory C)
  (f : type-hom-Precategory C y x)
  (g : type-hom-Precategory C z x)
  (w : obj-Precategory C)
  (p₁ : type-hom-Precategory C w y)
  (p₂ : type-hom-Precategory C w z)
  (α : comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂)
  where

  is-prop-is-pullback-Precategory :
    is-prop (is-pullback-Precategory C x y z f g w p₁ p₂ α)
  is-prop-is-pullback-Precategory =
    is-prop-Π (λ w' →
      is-prop-Π (λ p₁' →
        is-prop-Π (λ p₂' →
          is-prop-function-type
            is-property-is-contr)))

  is-pullback-Precategory-Prop : Prop (l1 ⊔ l2)
  pr1 is-pullback-Precategory-Prop =
    is-pullback-Precategory C x y z f g w p₁ p₂ α
  pr2 is-pullback-Precategory-Prop =
    is-prop-is-pullback-Precategory
```
