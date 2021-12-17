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
  (Fmap : {x y : obj-Precat C} (f : type-hom-Precat C x y) → type-hom-Precat D (F x) (F y)) where

  respects-comp-Precat : UU (l1 ⊔ l2 ⊔ l4)
  respects-comp-Precat = {x y z : obj-Precat C} (g : type-hom-Precat C y z) (f : type-hom-Precat C x y)
                       → Id (Fmap (g ∘⟦ C ⟧ f)) (Fmap g ∘⟦ D ⟧ Fmap f)

  respects-id-Precat : UU (l1 ⊔ l4)
  respects-id-Precat = (x : obj-Precat C) → Id (Fmap (id-Precat C x)) (id-Precat D (F x))

module _ {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4) where

  functor-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precat = Σ (obj-Precat C → obj-Precat D)
                     λ F → Σ ({x y : obj-Precat C} (f : type-hom-Precat C x y) → type-hom-Precat D (F x) (F y))
                             (λ Fmap → respects-comp-Precat C D F Fmap
                                     × respects-id-Precat C D F Fmap)

  obj-functor-Precat : functor-Precat → obj-Precat C → obj-Precat D
  obj-functor-Precat = pr1

  hom-functor-Precat : (F : functor-Precat)
                     → {x y : obj-Precat C}
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
                  → {x y : obj-Cat C}
                  → (f : type-hom-Cat C x y)
                  → type-hom-Cat D (obj-functor-Cat F x) (obj-functor-Cat F y)
  hom-functor-Cat F = pr1 (pr2 F)

  respects-comp-functor-Cat : (F : functor-Cat)
                            → respects-comp-Precat (precat-Cat C) (precat-Cat D) (obj-functor-Cat F) (hom-functor-Cat F)
  respects-comp-functor-Cat F = respects-comp-functor-Precat (precat-Cat C) (precat-Cat D) F

  respects-id-functor-Cat : (F : functor-Cat)
                          → respects-id-Precat (precat-Cat C) (precat-Cat D) (obj-functor-Cat F) (hom-functor-Cat F)
  respects-id-functor-Cat F = respects-id-functor-Precat (precat-Cat C) (precat-Cat D) F
```

There is an identity functor on any category.

```agda
id-functor-Precat : ∀ {l1 l2} (C : Precat l1 l2) → functor-Precat C C
pr1 (id-functor-Precat C) = id
pr1 (pr2 (id-functor-Precat C)) = id
pr1 (pr2 (pr2 (id-functor-Precat C))) g f = refl
pr2 (pr2 (pr2 (id-functor-Precat C))) x = refl

id-functor-Cat : ∀ {l1 l2} (C : Cat l1 l2) → functor-Cat C C
id-functor-Cat C = id-functor-Precat (precat-Cat C)
```

Two compatible functors can be composed.

```agda
comp-functor-Precat : ∀ {l1 l2 l3 l4 l5 l6}
                    → (C : Precat l1 l2)
                    → (D : Precat l3 l4)
                    → (E : Precat l5 l6)
                    → (G : functor-Precat D E)
                    → (F : functor-Precat C D)
                    → functor-Precat C E
pr1 (comp-functor-Precat C D E G F) =
  obj-functor-Precat D E G ∘ obj-functor-Precat C D F
pr1 (pr2 (comp-functor-Precat C D E G F)) =
  hom-functor-Precat D E G ∘ hom-functor-Precat C D F
pr1 (pr2 (pr2 (comp-functor-Precat C D E G F))) g f =
    ap (hom-functor-Precat D E G) (respects-comp-functor-Precat C D F g f)
  ∙ respects-comp-functor-Precat D E G (hom-functor-Precat C D F g) (hom-functor-Precat C D F f)
pr2 (pr2 (pr2 (comp-functor-Precat C D E G F))) x =
    ap (hom-functor-Precat D E G) (respects-id-functor-Precat C D F x)
  ∙ respects-id-functor-Precat D E G (obj-functor-Precat C D F x)

comp-functor-Cat : ∀ {l1 l2 l3 l4 l5 l6}
                 → (C : Cat l1 l2)
                 → (D : Cat l3 l4)
                 → (E : Cat l5 l6)
                 → (G : functor-Cat D E)
                 → (F : functor-Cat C D)
                 → functor-Cat C E
comp-functor-Cat C D E G F =
  comp-functor-Precat (precat-Cat C) (precat-Cat D) (precat-Cat E) G F
```


