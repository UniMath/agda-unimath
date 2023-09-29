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
- morphisms `p : hom w y` and `q : hom w z` such that
- `f ∘ p = g ∘ q` together with the universal property that for every object
  `w'` and pair of morphisms `p' : hom w' y` and `q' : hom w' z` such that
  `f ∘ p' = g ∘ q'` there exists a unique morphism `h : hom w' w` such that
- `p ∘ h = p'`
- `q ∘ h = q'`.

We say that `C` has all pullbacks if there is a choice of a pullback for each
object `x` and pair of morphisms into `x` in `C`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pullback-Precategory :
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    (g : hom-Precategory C z x) →
    (w : obj-Precategory C) →
    (p : hom-Precategory C w y) →
    (q : hom-Precategory C w z) →
    comp-hom-Precategory C f p ＝ comp-hom-Precategory C g q →
    UU (l1 ⊔ l2)
  is-pullback-Precategory x y z f g w p q _ =
    (w' : obj-Precategory C) →
    (p' : hom-Precategory C w' y) →
    (q' : hom-Precategory C w' z) →
    comp-hom-Precategory C f p' ＝ comp-hom-Precategory C g q' →
    ∃!
      ( hom-Precategory C w' w)
      ( λ h →
        ( comp-hom-Precategory C p h ＝ p') ×
        ( comp-hom-Precategory C q h ＝ q'))

  pullback-Precategory :
    (x y z : obj-Precategory C) →
    hom-Precategory C y x →
    hom-Precategory C z x →
    UU (l1 ⊔ l2)
  pullback-Precategory x y z f g =
    Σ (obj-Precategory C) λ w →
    Σ (hom-Precategory C w y) λ p →
    Σ (hom-Precategory C w z) λ q →
    Σ (comp-hom-Precategory C f p ＝ comp-hom-Precategory C g q) λ α →
      is-pullback-Precategory x y z f g w p q α

  has-all-pullbacks-Precategory : UU (l1 ⊔ l2)
  has-all-pullbacks-Precategory =
    (x y z : obj-Precategory C) →
    (f : hom-Precategory C y x) →
    (g : hom-Precategory C z x) →
    pullback-Precategory x y z f g

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : has-all-pullbacks-Precategory C)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  where

  object-pullback-Precategory : obj-Precategory C
  object-pullback-Precategory = pr1 (t x y z f g)

  pr1-pullback-Precategory :
    hom-Precategory C object-pullback-Precategory y
  pr1-pullback-Precategory = pr1 (pr2 (t x y z f g))

  pr2-pullback-Precategory :
    hom-Precategory C object-pullback-Precategory z
  pr2-pullback-Precategory = pr1 (pr2 (pr2 (t x y z f g)))

  pullback-square-Precategory-comm :
    comp-hom-Precategory C f pr1-pullback-Precategory ＝
    comp-hom-Precategory C g pr2-pullback-Precategory
  pullback-square-Precategory-comm = pr1 (pr2 (pr2 (pr2 (t x y z f g))))

  module _
    (w' : obj-Precategory C)
    (p' : hom-Precategory C w' y)
    (q' : hom-Precategory C w' z)
    (ε : comp-hom-Precategory C f p' ＝ comp-hom-Precategory C g q')
    where

    morphism-into-pullback-Precategory :
      hom-Precategory C w' object-pullback-Precategory
    morphism-into-pullback-Precategory =
      pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p' q' ε))

    morphism-into-pullback-comm-pr1-Precategory :
      comp-hom-Precategory C
        pr1-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      p'
    morphism-into-pullback-comm-pr1-Precategory =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p' q' ε)))

    morphism-into-pullback-comm-pr2-Precategory :
      comp-hom-Precategory C
        pr2-pullback-Precategory
        morphism-into-pullback-Precategory ＝
      q'
    morphism-into-pullback-comm-pr2-Precategory =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p' q' ε)))

    is-unique-morphism-into-pullback-Precategory :
      (h' : hom-Precategory C w' object-pullback-Precategory) →
      comp-hom-Precategory C pr1-pullback-Precategory h' ＝ p' →
      comp-hom-Precategory C pr2-pullback-Precategory h' ＝ q' →
      morphism-into-pullback-Precategory ＝ h'
    is-unique-morphism-into-pullback-Precategory h' η θ =
      ap
        ( pr1)
        ( pr2 (pr2 (pr2 (pr2 (pr2 (t x y z f g)))) w' p' q' ε) (h' , η , θ))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y z : obj-Precategory C)
  (f : hom-Precategory C y x)
  (g : hom-Precategory C z x)
  (w : obj-Precategory C)
  (p : hom-Precategory C w y)
  (q : hom-Precategory C w z)
  (ε : comp-hom-Precategory C f p ＝ comp-hom-Precategory C g q)
  where

  is-prop-is-pullback-Precategory :
    is-prop (is-pullback-Precategory C x y z f g w p q ε)
  is-prop-is-pullback-Precategory =
    is-prop-Π³ (λ w' p' q' → is-prop-function-type is-property-is-contr)

  is-pullback-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-pullback-prop-Precategory =
    is-pullback-Precategory C x y z f g w p q ε
  pr2 is-pullback-prop-Precategory =
    is-prop-is-pullback-Precategory
```
