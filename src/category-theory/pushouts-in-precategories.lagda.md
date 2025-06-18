# Pushouts in precategories

```agda
module category-theory.pushouts-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.pullbacks-in-precategories

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
{{#concept "pushout" Disambiguation="of objects in precategories" Agda=pushout-obj-Precategory}}
of two morphisms `f : hom x y` and `g : hom x z` in a category `C` consists of:

- an object `w`
- morphisms `i₁ : hom y w` and `i₂ : hom z w` such that
- `i₁ ∘ f = i₂ ∘ g` together with the universal property that for every
  object`w'` and pair of morphisms `i₁' : hom y w'` and `i₂' : hom z w'` such
  that `i₁' ∘ f = i₂' ∘ g` there exists a unique morphism `h : hom w w'` such
  that
- `h ∘ i₁ = i₁'`
- `h ∘ i₂ = i₂'`.

We say that `C`
{{#concept "has all pushouts" Disambiguation="precategory" Agda=has-all-pushout-obj-Precategory}}
if there is a choice of a pushout for each object `x` and pair of morphisms out
of `x` in `C`.

All definitions here are defined in terms of pullbacks in the
[opposite precategory](category-theory.opposite-precategories.md); see
[pullbacks](category-theory.pullbacks-in-precategories.md) for details.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pushout-obj-Precategory :
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C x y) →
    (g : hom-Precategory C x z) →
    (w : obj-Precategory C) →
    (i₁ : hom-Precategory C y w) →
    (i₂ : hom-Precategory C z w) →
    comp-hom-Precategory C i₁ f ＝ comp-hom-Precategory C i₂ g →
    UU (l1 ⊔ l2)
  is-pushout-obj-Precategory =
    is-pullback-obj-Precategory (opposite-Precategory C)

  pushout-obj-Precategory :
    (x y z : obj-Precategory C) →
    hom-Precategory C x y →
    hom-Precategory C x z →
    UU (l1 ⊔ l2)
  pushout-obj-Precategory =
    pullback-obj-Precategory (opposite-Precategory C)

  has-all-pushout-obj-Precategory : UU (l1 ⊔ l2)
  has-all-pushout-obj-Precategory =
    has-all-pullback-obj-Precategory (opposite-Precategory C)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-pushout-obj-Precategory C)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C x y)
  (g : hom-Precategory C x z)
  where

  object-pushout-obj-Precategory : obj-Precategory C
  object-pushout-obj-Precategory =
    object-pullback-obj-Precategory (opposite-Precategory C) t x y z f g

  inl-pushout-obj-Precategory :
    hom-Precategory C y object-pushout-obj-Precategory
  inl-pushout-obj-Precategory =
    pr1-pullback-obj-Precategory (opposite-Precategory C) t x y z f g

  inr-pushout-obj-Precategory :
    hom-Precategory C z object-pushout-obj-Precategory
  inr-pushout-obj-Precategory =
    pr2-pullback-obj-Precategory (opposite-Precategory C) t x y z f g

  comm-pushout-obj-Precategory :
    comp-hom-Precategory C inl-pushout-obj-Precategory f ＝
    comp-hom-Precategory C inr-pushout-obj-Precategory g
  comm-pushout-obj-Precategory =
    comm-pullback-obj-Precategory (opposite-Precategory C) t x y z f g

  module _
    (w' : obj-Precategory C)
    (i₁' : hom-Precategory C y w')
    (i₂' : hom-Precategory C z w')
    (α : comp-hom-Precategory C i₁' f ＝ comp-hom-Precategory C i₂' g)
    where

    morphism-from-pushout-obj-Precategory :
      hom-Precategory C object-pushout-obj-Precategory w'
    morphism-from-pushout-obj-Precategory =
      morphism-into-pullback-obj-Precategory (opposite-Precategory C)
        t x y z f g w' i₁' i₂' α

    comm-morphism-from-inl-pushout-obj-Precategory :
      comp-hom-Precategory C
        morphism-from-pushout-obj-Precategory
        inl-pushout-obj-Precategory ＝
      i₁'
    comm-morphism-from-inl-pushout-obj-Precategory =
      comm-morphism-into-pr1-pullback-obj-Precategory (opposite-Precategory C)
        t x y z f g w' i₁' i₂' α

    comm-morphism-from-inr-pushout-obj-Precategory :
      comp-hom-Precategory C
        morphism-from-pushout-obj-Precategory
        inr-pushout-obj-Precategory ＝
      i₂'
    comm-morphism-from-inr-pushout-obj-Precategory =
      comm-morphism-into-pr2-pullback-obj-Precategory (opposite-Precategory C)
        t x y z f g w' i₁' i₂' α

    is-unique-morphism-from-pushout-obj-Precategory :
      (h' : hom-Precategory C object-pushout-obj-Precategory w') →
      comp-hom-Precategory C h' inl-pushout-obj-Precategory ＝ i₁' →
      comp-hom-Precategory C h' inr-pushout-obj-Precategory ＝ i₂' →
      morphism-from-pushout-obj-Precategory ＝ h'
    is-unique-morphism-from-pushout-obj-Precategory =
      is-unique-morphism-into-pullback-obj-Precategory (opposite-Precategory C)
        t x y z f g w' i₁' i₂' α

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C x y)
  (g : hom-Precategory C x z)
  (w : obj-Precategory C)
  (i₁ : hom-Precategory C y w)
  (i₂ : hom-Precategory C z w)
  (α : comp-hom-Precategory C i₁ f ＝ comp-hom-Precategory C i₂ g)
  where

  is-prop-is-pushout-obj-Precategory :
    is-prop (is-pushout-obj-Precategory C x y z f g w i₁ i₂ α)
  is-prop-is-pushout-obj-Precategory =
    is-prop-is-pullback-obj-Precategory (opposite-Precategory C)
      x y z f g w i₁ i₂ α

  is-pushout-prop-Precategory : Prop (l1 ⊔ l2)
  is-pushout-prop-Precategory =
    is-pullback-prop-Precategory (opposite-Precategory C) x y z f g w i₁ i₂ α
```

## See also

- [Pullbacks](category-theory.pullbacks-in-precategories.md) for the dual
  concept.
