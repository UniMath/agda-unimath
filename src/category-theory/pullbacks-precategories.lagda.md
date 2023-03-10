# Pullbacks in precategories

```agda
module category-theory.pullbacks-precategories where
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

A pullback of two morphisms `f : hom y x` and `g : hom z x` in a category `C` consists of:
- an object `w`
- morphisms `p₁ : hom w y` and `p₂ : hom w z`
such that
- `comp f p₁ = comp g p₂`
together with the universal property that for every object `w'` and pair of morphisms `p₁' : hom w' y` and `p₂' : hom w' z` such that `comp f p₁' = comp g p₂'` there exists a unique morphism `h : hom w' w` such that
- `comp p₁ h = p₁'`
- `comp p₂ h = p₂'`.

We say that `C` has all pullbacks if there is a choice of a pullback for each object `x` and pair of morphisms into `x` in `C`.

## Definition

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) where

  is-pullback :
    (x y z : obj-Precat C) →
    (f : type-hom-Precat C y x) →
    (g : type-hom-Precat C z x) →
    (w : obj-Precat C) →
    (p₁ : type-hom-Precat C w y) →
    (p₂ : type-hom-Precat C w z) →
    comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂ →
    UU (l1 ⊔ l2)
  is-pullback x y z f g w p₁ p₂ _ =
    (w' : obj-Precat C) →
    (p₁' : type-hom-Precat C w' y) →
    (p₂' : type-hom-Precat C w' z) →
    comp-hom-Precat C f p₁' ＝ comp-hom-Precat C g p₂' →
    ∃! (type-hom-Precat C w' w) λ h →
       (comp-hom-Precat C p₁ h ＝ p₁') ×
       (comp-hom-Precat C p₂ h ＝ p₂')

  pullback :
    (x y z : obj-Precat C) →
    type-hom-Precat C y x →
    type-hom-Precat C z x →
    UU (l1 ⊔ l2)
  pullback x y z f g =
    Σ (obj-Precat C) λ w →
    Σ (type-hom-Precat C w y) λ p₁ →
    Σ (type-hom-Precat C w z) λ p₂ →
    Σ (comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂) λ α →
      is-pullback x y z f g w p₁ p₂ α

  has-all-pullbacks : UU (l1 ⊔ l2)
  has-all-pullbacks =
    (x y z : obj-Precat C) →
    (f : type-hom-Precat C y x) →
    (g : type-hom-Precat C z x) →
    pullback x y z f g

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-pullbacks C)
  (x y z : obj-Precat C)
  (f : type-hom-Precat C y x)
  (g : type-hom-Precat C z x) where

  object-pullback : obj-Precat C
  object-pullback = pr1 (t x y z f g)

  proj₁-pullback : type-hom-Precat C object-pullback y
  proj₁-pullback = pr1 (pr2 (t x y z f g))

  proj₂-pullback : type-hom-Precat C object-pullback z
  proj₂-pullback = pr1 (pr2 (pr2 (t x y z f g)))

  pullback-square-comm :
    comp-hom-Precat C f proj₁-pullback ＝ comp-hom-Precat C g proj₂-pullback
  pullback-square-comm = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _ (w' : obj-Precat C)
    (p₁' : type-hom-Precat C w' y)
    (p₂' : type-hom-Precat C w' z)
    (α : comp-hom-Precat C f p₁' ＝ comp-hom-Precat C g p₂') where

    morphism-into-pullback : type-hom-Precat C w' object-pullback
    morphism-into-pullback =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α))

    morphism-into-pullback-comm-proj₁ :
      comp-hom-Precat C proj₁-pullback morphism-into-pullback ＝ p₁'
    morphism-into-pullback-comm-proj₁ =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    morphism-into-pullback-comm-proj₂ :
      comp-hom-Precat C proj₂-pullback morphism-into-pullback ＝ p₂'
    morphism-into-pullback-comm-proj₂ =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    is-unique-morphism-into-pullback :
      (h' : type-hom-Precat C w' object-pullback) →
      comp-hom-Precat C proj₁-pullback h' ＝ p₁' →
      comp-hom-Precat C proj₂-pullback h' ＝ p₂' →
      morphism-into-pullback ＝ h'
    is-unique-morphism-into-pullback h' α₁ α₂ =
      ap pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α) (h' , α₁ , α₂))

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (x y z : obj-Precat C)
  (f : type-hom-Precat C y x)
  (g : type-hom-Precat C z x)
  (w : obj-Precat C)
  (p₁ : type-hom-Precat C w y)
  (p₂ : type-hom-Precat C w z)
  (α : comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂) where

  is-prop-is-pullback : is-prop (is-pullback C x y z f g w p₁ p₂ α)
  is-prop-is-pullback =
    is-prop-Π (λ w' →
      is-prop-Π (λ p₁' →
        is-prop-Π (λ p₂' →
          is-prop-function-type
            is-property-is-contr)))

  is-pullback-Prop : Prop (l1 ⊔ l2)
  pr1 is-pullback-Prop = is-pullback C x y z f g w p₁ p₂ α
  pr2 is-pullback-Prop = is-prop-is-pullback
```
