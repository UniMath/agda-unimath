# Categories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.categories where

open import categories.isomorphisms-precategories using
  ( iso-Precat; id-iso-Precat)
open import categories.precategories using
  ( Precat; obj-Precat; id-Precat; hom-Precat; type-hom-Precat;
    is-set-type-hom-Precat; comp-Precat; assoc-comp-Precat;
    left-unit-law-comp-Precat; right-unit-law-comp-Precat)
open import foundation.dependent-pair-types using (Σ; pr1; pr2)
open import foundation.equivalences using (is-equiv-Prop)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using (UU-Prop; Π-Prop; type-Prop)
open import foundation.sets using (UU-Set; is-set)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
```

## Idea

A category in Homotopy Type Theory is a precategory for which the identities between the objects are exactly the isomorphisms. More exactly, an equality between objects `x y : A` gives rise to an isomorphism between them, by the J-rule. A precategory is a category if this function is an equivalence.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  iso-eq-Precat : (x y : obj-Precat C) → Id x y → iso-Precat C x y
  iso-eq-Precat x .x refl = id-iso-Precat C

  is-category-Precat-Prop : UU-Prop (l1 ⊔ l2)
  is-category-Precat-Prop =
    Π-Prop (obj-Precat C)
      ( λ x → Π-Prop (obj-Precat C) (λ y → is-equiv-Prop (iso-eq-Precat x y)))

  is-category-Precat : UU (l1 ⊔ l2)
  is-category-Precat = type-Prop is-category-Precat-Prop

Cat : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cat l1 l2 = Σ (Precat l1 l2) is-category-Precat

module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  precat-Cat : Precat l1 l2
  precat-Cat = pr1 C

  obj-Cat : UU l1
  obj-Cat = obj-Precat precat-Cat

  hom-Cat : obj-Cat → obj-Cat → UU-Set l2
  hom-Cat = hom-Precat precat-Cat

  type-hom-Cat : obj-Cat → obj-Cat → UU l2
  type-hom-Cat = type-hom-Precat precat-Cat

  is-set-type-hom-Cat : (x y : obj-Cat) → is-set (type-hom-Cat x y)
  is-set-type-hom-Cat = is-set-type-hom-Precat precat-Cat

  comp-Cat : {x y z : obj-Cat} → type-hom-Cat y z → type-hom-Cat x y → type-hom-Cat x z
  comp-Cat = comp-Precat precat-Cat

  assoc-comp-Cat :
    {x y z w : obj-Cat}
    (h : type-hom-Cat z w) (g : type-hom-Cat y z) (f : type-hom-Cat x y) →
    Id ( comp-Cat (comp-Cat h g) f)
       ( comp-Cat h (comp-Cat g f))
  assoc-comp-Cat = assoc-comp-Precat precat-Cat

  id-Cat : {x : obj-Cat} → type-hom-Cat x x
  id-Cat = id-Precat precat-Cat

  left-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat id-Cat f) f
  left-unit-law-comp-Cat = left-unit-law-comp-Precat precat-Cat

  right-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat f id-Cat) f
  right-unit-law-comp-Cat = right-unit-law-comp-Precat precat-Cat
```
