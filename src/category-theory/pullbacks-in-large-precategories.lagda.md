# Pullbacks in large precategories

```agda
module category-theory.pullbacks-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

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
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 l4 : Level}
  where

  is-pullback-Large-Precategory :
    {x : obj-Large-Precategory C l1}
    {y : obj-Large-Precategory C l2}
    {z : obj-Large-Precategory C l3}
    {w : obj-Large-Precategory C l4}
    (f : hom-Large-Precategory C y x)
    (g : hom-Large-Precategory C z x) →
    (p₁ : hom-Large-Precategory C w y) →
    (p₂ : hom-Large-Precategory C w z) →
    comp-hom-Large-Precategory C f p₁ ＝ comp-hom-Large-Precategory C g p₂ →
    UU (α l1 ⊔ β l1 l1 ⊔ β l1 l2 ⊔ β l1 l3 ⊔ β l1 l4)
  is-pullback-Large-Precategory x y z f g w p₁ p₂ _ =
    (w' : obj-Large-Precategory C l1) →
    (p₁' : hom-Large-Precategory C w' y) →
    (p₂' : hom-Large-Precategory C w' z) →
    comp-hom-Large-Precategory C f p₁' ＝ comp-hom-Large-Precategory C g p₂' →
    ∃!
      ( hom-Large-Precategory C w' w)
      ( λ h →
        ( comp-hom-Large-Precategory C p₁ h ＝ p₁') ×
        ( comp-hom-Large-Precategory C p₂ h ＝ p₂'))

  pullback-Large-Precategory :
    (x : obj-Large-Precategory C l1) →
    (y : obj-Large-Precategory C l2) →
    (z : obj-Large-Precategory C l3) →
    hom-Large-Precategory C y x →
    hom-Large-Precategory C z x →
    UU (α l1 ⊔ α l4 ⊔ β l1 l1 ⊔ β l1 l2 ⊔ β l1 l3 ⊔
        β l1 l4 ⊔ β l4 l1 ⊔ β l4 l2 ⊔ β l4 l3)
  pullback-Large-Precategory x y z f g =
    Σ (obj-Large-Precategory C l4) λ w →
    Σ (hom-Large-Precategory C w y) λ p₁ →
    Σ (hom-Large-Precategory C w z) λ p₂ →
    Σ (comp-hom-Large-Precategory C f p₁
    ＝ comp-hom-Large-Precategory C g p₂) λ α →
      is-pullback-Large-Precategory x y z f g w p₁ p₂ α

  has-all-pullbacks-Large-Precategory :
    UU (α l1 ⊔ α l2 ⊔ α l3 ⊔ α l4 ⊔ β l1 l1 ⊔ β l1 l2 ⊔ β l1 l3 ⊔
        β l1 l4 ⊔ β l2 l1 ⊔ β l3 l1 ⊔ β l4 l1 ⊔ β l4 l2 ⊔ β l4 l3)
  has-all-pullbacks-Large-Precategory =
    (x : obj-Large-Precategory C l1) →
    (y : obj-Large-Precategory C l2) →
    (z : obj-Large-Precategory C l3) →
    (f : hom-Large-Precategory C y x) →
    (g : hom-Large-Precategory C z x) →
    pullback-Large-Precategory x y z f g

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (t : has-all-pullbacks-Large-Precategory C)
  (x y z : obj-Large-Precategory C l1)
  (f : hom-Large-Precategory C y x)
  (g : hom-Large-Precategory C z x)
  where

  object-pullback-Large-Precategory : obj-Large-Precategory C l2
  object-pullback-Large-Precategory = pr1 (t x y z f g)

  pr1-pullback-Large-Precategory :
    hom-Large-Precategory C object-pullback-Large-Precategory y
  pr1-pullback-Large-Precategory = pr1 (pr2 (t x y z f g))

  pr2-pullback-Large-Precategory :
    hom-Large-Precategory C object-pullback-Large-Precategory z
  pr2-pullback-Large-Precategory = pr1 (pr2 (pr2 (t x y z f g)))

  pullback-square-Large-Precategory-comm :
    comp-hom-Large-Precategory C f pr1-pullback-Large-Precategory ＝
    comp-hom-Large-Precategory C g pr2-pullback-Large-Precategory
  pullback-square-Large-Precategory-comm = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _
    (w' : obj-Large-Precategory C l1)
    (p₁' : hom-Large-Precategory C w' y)
    (p₂' : hom-Large-Precategory C w' z)
    (α : comp-hom-Large-Precategory C f p₁'
      ＝ comp-hom-Large-Precategory C g p₂')
    where

    morphism-into-pullback-Large-Precategory :
      hom-Large-Precategory C w' object-pullback-Large-Precategory
    morphism-into-pullback-Large-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α))

    morphism-into-pullback-comm-pr1-Large-Precategory :
      comp-hom-Large-Precategory C
        pr1-pullback-Large-Precategory
        morphism-into-pullback-Large-Precategory ＝
      p₁'
    morphism-into-pullback-comm-pr1-Large-Precategory =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    morphism-into-pullback-comm-pr2-Large-Precategory :
      comp-hom-Large-Precategory C
        pr2-pullback-Large-Precategory
        morphism-into-pullback-Large-Precategory ＝
      p₂'
    morphism-into-pullback-comm-pr2-Large-Precategory =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    is-unique-morphism-into-pullback-Large-Precategory :
      (h' : hom-Large-Precategory C w' object-pullback-Large-Precategory) →
      comp-hom-Large-Precategory C pr1-pullback-Large-Precategory h' ＝ p₁' →
      comp-hom-Large-Precategory C pr2-pullback-Large-Precategory h' ＝ p₂' →
      morphism-into-pullback-Large-Precategory ＝ h'
    is-unique-morphism-into-pullback-Large-Precategory h' α₁ α₂ =
      ap
        ( pr1)
        ( pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α) (h' , α₁ , α₂))

module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 l2 l3 l4 : Level} (C : Large-Precategory α β)
  (x : obj-Large-Precategory C l1)
  (y : obj-Large-Precategory C l2)
  (z : obj-Large-Precategory C l3)
  (f : hom-Large-Precategory C y x)
  (g : hom-Large-Precategory C z x)
  (w : obj-Large-Precategory C l4)
  (p₁ : hom-Large-Precategory C w y)
  (p₂ : hom-Large-Precategory C w z)
  (α₁ : comp-hom-Large-Precategory C f p₁ ＝ comp-hom-Large-Precategory C g p₂)
  where

  is-prop-is-pullback-Large-Precategory :
    is-prop (is-pullback-Large-Precategory C x y z f g w p₁ p₂ α₁)
  is-prop-is-pullback-Large-Precategory =
    is-prop-Π³ (λ w' p₁' p₂' → is-prop-function-type is-property-is-contr)

  is-pullback-prop-Large-Precategory :
    Prop (α l1 ⊔ β l1 l1 ⊔ β l1 l2 ⊔ β l1 l3 ⊔ β l1 l4)
  pr1 is-pullback-prop-Large-Precategory =
    is-pullback-Large-Precategory C x y z f g w p₁ p₂ α₁
  pr2 is-pullback-prop-Large-Precategory =
    is-prop-is-pullback-Large-Precategory
```
