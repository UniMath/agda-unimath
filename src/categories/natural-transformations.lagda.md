---
title: Formalisation of the Symmetry Book
---

Natural transformations.

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.natural-transformations where

open import categories.functors public

module _ {l1 l2 l3 l4}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F G : functor-Precat C D) where

  is-nat-trans-Precat : ((x : obj-Precat C) → type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x))
                      → UU (l1 ⊔ l2 ⊔ l4)
  is-nat-trans-Precat γ = {x y : obj-Precat C} (f : type-hom-Precat C x y)
                        → Id (comp-Precat D (hom-functor-Precat C D G f) (γ x)) (comp-Precat D (γ y) (hom-functor-Precat C D F f))

  is-prop-is-nat-trans-Precat : (γ : (x : obj-Precat C) → type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x))
                              → is-prop (is-nat-trans-Precat γ)
  is-prop-is-nat-trans-Precat γ =
    is-prop-Π' (λ x →
      is-prop-Π' (λ y →
        is-prop-Π (λ f →
          is-set-type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G y)
                                   (comp-Precat D (hom-functor-Precat C D G f) (γ x)) (comp-Precat D (γ y) (hom-functor-Precat C D F f)))))

  nat-trans-Precat : UU (l1 ⊔ l2 ⊔ l4)
  nat-trans-Precat =
    Σ ((x : obj-Precat C) → type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x))
      is-nat-trans-Precat

  components-nat-trans-Precat : nat-trans-Precat
                              → (x : obj-Precat C)
                              → type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x)
  components-nat-trans-Precat = pr1

  is-nat-iso-Precat : nat-trans-Precat → UU (l1 ⊔ l4)
  is-nat-iso-Precat γ = (x : obj-Precat C) → is-iso-Precat D (components-nat-trans-Precat γ x)

  is-prop-is-nat-iso-Precat : (γ : nat-trans-Precat) → is-prop (is-nat-iso-Precat γ)
  is-prop-is-nat-iso-Precat γ =
    is-prop-Π (λ x → is-prop-is-iso-Precat D (components-nat-trans-Precat γ x))

  nat-iso-Precat : UU (l1 ⊔ l2 ⊔ l4)
  nat-iso-Precat =
    Σ nat-trans-Precat is-nat-iso-Precat

module _ {l1 l2 l3 l4}
  (C : Cat l1 l2)
  (D : Cat l3 l4)
  (F G : functor-Cat C D) where

  is-nat-trans-Cat : ((x : obj-Cat C) → type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x))
                   → UU (l1 ⊔ l2 ⊔ l4)
  is-nat-trans-Cat = is-nat-trans-Precat (precat-Cat C) (precat-Cat D) F G

  nat-trans-Cat : UU (l1 ⊔ l2 ⊔ l4)
  nat-trans-Cat = nat-trans-Precat (precat-Cat C) (precat-Cat D) F G

  components-nat-trans-Cat : nat-trans-Cat → (x : obj-Cat C) → type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x)
  components-nat-trans-Cat = components-nat-trans-Precat (precat-Cat C) (precat-Cat D) F G

  is-nat-iso-Cat : nat-trans-Cat → UU (l1 ⊔ l4)
  is-nat-iso-Cat = is-nat-iso-Precat (precat-Cat C) (precat-Cat D) F G

  nat-iso-Cat : UU (l1 ⊔ l2 ⊔ l4)
  nat-iso-Cat = nat-iso-Precat (precat-Cat C) (precat-Cat D) F G
```

Equivalences of categories.

```agda
module _ {l1 l2 l3 l4}
  (C : Precat l1 l2)
  (D : Precat l3 l4) where

  is-equiv-functor-Precat : functor-Precat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Precat F =
    Σ (functor-Precat D C)
      λ G → nat-iso-Precat C C (comp-functor-Precat C D C G F) (id-functor-Precat C)
          × nat-iso-Precat D D (comp-functor-Precat D C D F G) (id-functor-Precat D)

  equiv-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Precat = Σ (functor-Precat C D) is-equiv-functor-Precat

module _ {l1 l2 l3 l4}
  (C : Cat l1 l2)
  (D : Cat l3 l4) where

  is-equiv-functor-Cat : functor-Cat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Cat = is-equiv-functor-Precat (precat-Cat C) (precat-Cat D)

  equiv-Cat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Cat = equiv-Precat (precat-Cat C) (precat-Cat D)
```
