# Natural transformations between functors on categories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.natural-transformations-categories where

open import categories.categories using
  ( Cat; obj-Cat; type-hom-Cat; precat-Cat)
open import categories.functors-categories using
  ( functor-Cat; obj-functor-Cat)
open import categories.natural-transformations-precategories using
  ( is-nat-trans-Precat; nat-trans-Precat; components-nat-trans-Precat)
open import foundation.universe-levels using (UU; _⊔_)
```

## Idea

A natural transformation between functors on categories is a natural transformation between the functors on the underlying precategories.

```agda
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
```
