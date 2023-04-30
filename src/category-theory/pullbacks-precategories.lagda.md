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

A pullback of two morphisms `f : hom y x` and `g : hom z x` in a category `C`
consists of:

- an object `w`
- morphisms `p₁ : hom w y` and `p₂ : hom w z` such that
- `compose f p₁ = compose g p₂` together with the universal property that for
  every object `w'` and pair of morphisms `p₁' : hom w' y` and `p₂' : hom w' z`
  such that `compose f p₁' = compose g p₂'` there exists a unique morphism
  `h : hom w' w` such that
- `compose p₁ h = p₁'`
- `compose p₂ h = p₂'`.

We say that `C` has all pullbacks if there is a choice of a pullback for each
object `x` and pair of morphisms into `x` in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-pullback-Precat :
    (x y z : obj-Precat C) →
    (f : type-hom-Precat C y x) →
    (g : type-hom-Precat C z x) →
    (w : obj-Precat C) →
    (p₁ : type-hom-Precat C w y) →
    (p₂ : type-hom-Precat C w z) →
    comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂ →
    UU (l1 ⊔ l2)
  is-pullback-Precat x y z f g w p₁ p₂ _ =
    (w' : obj-Precat C) →
    (p₁' : type-hom-Precat C w' y) →
    (p₂' : type-hom-Precat C w' z) →
    comp-hom-Precat C f p₁' ＝ comp-hom-Precat C g p₂' →
    ∃! (type-hom-Precat C w' w) λ h →
       (comp-hom-Precat C p₁ h ＝ p₁') ×
       (comp-hom-Precat C p₂ h ＝ p₂')

  pullback-Precat :
    (x y z : obj-Precat C) →
    type-hom-Precat C y x →
    type-hom-Precat C z x →
    UU (l1 ⊔ l2)
  pullback-Precat x y z f g =
    Σ (obj-Precat C) λ w →
    Σ (type-hom-Precat C w y) λ p₁ →
    Σ (type-hom-Precat C w z) λ p₂ →
    Σ (comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂) λ α →
      is-pullback-Precat x y z f g w p₁ p₂ α

  has-all-pullback-Precat : UU (l1 ⊔ l2)
  has-all-pullback-Precat =
    (x y z : obj-Precat C) →
    (f : type-hom-Precat C y x) →
    (g : type-hom-Precat C z x) →
    pullback-Precat x y z f g

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-pullback-Precat C)
  (x y z : obj-Precat C)
  (f : type-hom-Precat C y x)
  (g : type-hom-Precat C z x)
  where

  object-pullback-Precat : obj-Precat C
  object-pullback-Precat = pr1 (t x y z f g)

  pr1-pullback-Precat : type-hom-Precat C object-pullback-Precat y
  pr1-pullback-Precat = pr1 (pr2 (t x y z f g))

  pr2-pullback-Precat : type-hom-Precat C object-pullback-Precat z
  pr2-pullback-Precat = pr1 (pr2 (pr2 (t x y z f g)))

  pullback-square-Precat-comm :
    comp-hom-Precat C f pr1-pullback-Precat ＝
    comp-hom-Precat C g pr2-pullback-Precat
  pullback-square-Precat-comm = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _
    (w' : obj-Precat C)
    (p₁' : type-hom-Precat C w' y)
    (p₂' : type-hom-Precat C w' z)
    (α : comp-hom-Precat C f p₁' ＝ comp-hom-Precat C g p₂')
    where

    morphism-into-pullback-Precat : type-hom-Precat C w' object-pullback-Precat
    morphism-into-pullback-Precat =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α))

    morphism-into-pullback-comm-pr1 :
      comp-hom-Precat C pr1-pullback-Precat morphism-into-pullback-Precat ＝
      p₁'
    morphism-into-pullback-comm-pr1 =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    morphism-into-pullback-comm-pr2 :
      comp-hom-Precat C pr2-pullback-Precat morphism-into-pullback-Precat ＝
      p₂'
    morphism-into-pullback-comm-pr2 =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    is-unique-morphism-into-pullback-Precat :
      (h' : type-hom-Precat C w' object-pullback-Precat) →
      comp-hom-Precat C pr1-pullback-Precat h' ＝ p₁' →
      comp-hom-Precat C pr2-pullback-Precat h' ＝ p₂' →
      morphism-into-pullback-Precat ＝ h'
    is-unique-morphism-into-pullback-Precat h' α₁ α₂ =
      ap
        ( pr1)
        ( pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α) (h' , α₁ , α₂))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (x y z : obj-Precat C)
  (f : type-hom-Precat C y x)
  (g : type-hom-Precat C z x)
  (w : obj-Precat C)
  (p₁ : type-hom-Precat C w y)
  (p₂ : type-hom-Precat C w z)
  (α : comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂)
  where

  is-prop-is-pullback-Precat :
    is-prop (is-pullback-Precat C x y z f g w p₁ p₂ α)
  is-prop-is-pullback-Precat =
    is-prop-Π (λ w' →
      is-prop-Π (λ p₁' →
        is-prop-Π (λ p₂' →
          is-prop-function-type
            is-property-is-contr)))

  is-pullback-Precat-Prop : Prop (l1 ⊔ l2)
  pr1 is-pullback-Precat-Prop = is-pullback-Precat C x y z f g w p₁ p₂ α
  pr2 is-pullback-Precat-Prop = is-prop-is-pullback-Precat
```
