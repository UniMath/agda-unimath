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
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.uniqueness-quantification
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "pullback" Disambiguation="of objects in precategories" Agda=pullback-obj-Precategory}}
of two morphisms `f : hom y x` and `g : hom z x` in a category `C` consists of:

- an object `w`
- morphisms `p₁ : hom w y` and `p₂ : hom w z` such that
- `f ∘ p₁ = g ∘ p₂` together with the universal property that for every object
  `w'` and pair of morphisms `p₁' : hom w' y` and `p₂' : hom w' z` such that
  `f ∘ p₁' = g ∘ p₂'` there exists a unique morphism `h : hom w' w` such that
- `p₁ ∘ h = p₁'`
- `p₂ ∘ h = p₂'`.

We say that `C`
{{#concept "has all pullbacks" Disambiguation="precategory" Agda=has-all-pullback-obj-Precategory}}
if there is a choice of a pullback for each object `x` and pair of morphisms
into `x` in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pullback-obj-Precategory :
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    (g : hom-Precategory C z x) →
    (w : obj-Precategory C) →
    (p₁ : hom-Precategory C w y) →
    (p₂ : hom-Precategory C w z) →
    comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂ →
    UU (l1 ⊔ l2)
  is-pullback-obj-Precategory x y z f g w p₁ p₂ _ =
    (w' : obj-Precategory C) →
    (p₁' : hom-Precategory C w' y) →
    (p₂' : hom-Precategory C w' z) →
    comp-hom-Precategory C f p₁' ＝ comp-hom-Precategory C g p₂' →
    uniquely-exists-structure
      ( hom-Precategory C w' w)
      ( λ h →
        ( comp-hom-Precategory C p₁ h ＝ p₁') ×
        ( comp-hom-Precategory C p₂ h ＝ p₂'))

  pullback-obj-Precategory :
    (x y z : obj-Precategory C) →
    hom-Precategory C y x →
    hom-Precategory C z x →
    UU (l1 ⊔ l2)
  pullback-obj-Precategory x y z f g =
    Σ (obj-Precategory C) λ w →
    Σ (hom-Precategory C w y) λ p₁ →
    Σ (hom-Precategory C w z) λ p₂ →
    Σ (comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂) λ α →
      is-pullback-obj-Precategory x y z f g w p₁ p₂ α

  has-all-pullback-obj-Precategory : UU (l1 ⊔ l2)
  has-all-pullback-obj-Precategory =
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    (g : hom-Precategory C z x) →
    pullback-obj-Precategory x y z f g

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-pullback-obj-Precategory C)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  where

  object-pullback-obj-Precategory : obj-Precategory C
  object-pullback-obj-Precategory = pr1 (t x y z f g)

  pr1-pullback-obj-Precategory :
    hom-Precategory C object-pullback-obj-Precategory y
  pr1-pullback-obj-Precategory = pr1 (pr2 (t x y z f g))

  pr2-pullback-obj-Precategory :
    hom-Precategory C object-pullback-obj-Precategory z
  pr2-pullback-obj-Precategory = pr1 (pr2 (pr2 (t x y z f g)))

  comm-pullback-obj-Precategory :
    comp-hom-Precategory C f pr1-pullback-obj-Precategory ＝
    comp-hom-Precategory C g pr2-pullback-obj-Precategory
  comm-pullback-obj-Precategory = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _
    (w' : obj-Precategory C)
    (p₁' : hom-Precategory C w' y)
    (p₂' : hom-Precategory C w' z)
    (α : comp-hom-Precategory C f p₁' ＝ comp-hom-Precategory C g p₂')
    where

    morphism-into-pullback-obj-Precategory :
      hom-Precategory C w' object-pullback-obj-Precategory
    morphism-into-pullback-obj-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α))

    comm-morphism-into-pr1-pullback-obj-Precategory :
      comp-hom-Precategory C
        pr1-pullback-obj-Precategory
        morphism-into-pullback-obj-Precategory ＝
      p₁'
    comm-morphism-into-pr1-pullback-obj-Precategory =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    comm-morphism-into-pr2-pullback-obj-Precategory :
      comp-hom-Precategory C
        pr2-pullback-obj-Precategory
        morphism-into-pullback-obj-Precategory ＝
      p₂'
    comm-morphism-into-pr2-pullback-obj-Precategory =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α)))

    is-unique-morphism-into-pullback-obj-Precategory :
      (h' : hom-Precategory C w' object-pullback-obj-Precategory) →
      comp-hom-Precategory C pr1-pullback-obj-Precategory h' ＝ p₁' →
      comp-hom-Precategory C pr2-pullback-obj-Precategory h' ＝ p₂' →
      morphism-into-pullback-obj-Precategory ＝ h'
    is-unique-morphism-into-pullback-obj-Precategory h' α₁ α₂ =
      ap
        ( pr1)
        ( pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p₁' p₂' α) (h' , α₁ , α₂))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  (w : obj-Precategory C)
  (p₁ : hom-Precategory C w y)
  (p₂ : hom-Precategory C w z)
  (α : comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂)
  where

  is-prop-is-pullback-obj-Precategory :
    is-prop (is-pullback-obj-Precategory C x y z f g w p₁ p₂ α)
  is-prop-is-pullback-obj-Precategory =
    is-prop-iterated-Π 3
      ( λ w' p₁' p₂' → is-prop-function-type is-property-is-contr)

  is-pullback-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-pullback-prop-Precategory =
    is-pullback-obj-Precategory C x y z f g w p₁ p₂ α
  pr2 is-pullback-prop-Precategory =
    is-prop-is-pullback-obj-Precategory
```

## See also

- [Pushouts](category-theory.pushouts-in-precategories.md) for the dual
  concept.
