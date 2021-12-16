---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.functors where

open import categories.categories public

module _ {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F : obj-Precat C → obj-Precat D)
  (Fmap : (x y : obj-Precat C) (f : type-hom-Precat C x y) → type-hom-Precat D (F x) (F y)) where

  respects-comp-Precat : UU (l1 ⊔ l2 ⊔ l4)
  respects-comp-Precat = (x y z : obj-Precat C) (g : type-hom-Precat C y z) (f : type-hom-Precat C x y)
                       → Id (Fmap x z (comp-Precat C x y z g f)) (comp-Precat D (F x) (F y) (F z) (Fmap y z g) (Fmap x y f))

  respects-id-Precat : UU (l1 ⊔ l4)
  respects-id-Precat = (x : obj-Precat C) → Id (Fmap x x (id-Precat C x)) (id-Precat D (F x))

module _ {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4) where

  functor-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precat = Σ (obj-Precat C → obj-Precat D)
                     λ F → Σ ((x y : obj-Precat C) (f : type-hom-Precat C x y) → type-hom-Precat D (F x) (F y))
                             (λ Fmap → respects-comp-Precat C D F Fmap
                                     × respects-id-Precat C D F Fmap)

  obj-functor-Precat : functor-Precat → obj-Precat C → obj-Precat D
  obj-functor-Precat = pr1

  hom-functor-Precat : (F : functor-Precat)
                     → (x y : obj-Precat C)
                     → (f : type-hom-Precat C x y)
                     → type-hom-Precat D (obj-functor-Precat F x) (obj-functor-Precat F y)
  hom-functor-Precat F = pr1 (pr2 F)

  respects-comp-functor-Precat : (F : functor-Precat)
                               → respects-comp-Precat C D (obj-functor-Precat F) (hom-functor-Precat F)
  respects-comp-functor-Precat F = pr1 (pr2 (pr2 F))

  respects-id-functor-Precat : (F : functor-Precat)
                             → respects-id-Precat C D (obj-functor-Precat F) (hom-functor-Precat F)
  respects-id-functor-Precat F = pr2 (pr2 (pr2 F))

module _ {l1 l2 l3 l4 : Level}
  (C : Cat l1 l2)
  (D : Cat l3 l4) where

  functor-Cat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Cat = functor-Precat (precat-Cat C) (precat-Cat D)

  obj-functor-Cat : functor-Cat → obj-Cat C → obj-Cat D
  obj-functor-Cat = pr1

  hom-functor-Cat : (F : functor-Cat)
                  → (x y : obj-Cat C)
                  → (f : type-hom-Cat C x y)
                  → type-hom-Cat D (obj-functor-Cat F x) (obj-functor-Cat F y)
  hom-functor-Cat F = pr1 (pr2 F)

  respects-comp-functor-Cat : (F : functor-Cat)
                            → respects-comp-Precat (precat-Cat C) (precat-Cat D) (obj-functor-Cat F) (hom-functor-Cat F)
  respects-comp-functor-Cat F = respects-comp-functor-Precat (precat-Cat C) (precat-Cat D) F

  respects-id-functor-Cat : (F : functor-Cat)
                          → respects-id-Precat (precat-Cat C) (precat-Cat D) (obj-functor-Cat F) (hom-functor-Cat F)
  respects-id-functor-Cat F = respects-id-functor-Precat (precat-Cat C) (precat-Cat D) F

{-
TODO:
  * Identity functor
  * Composition of functors
  * When is a functor an equivalence
-}
