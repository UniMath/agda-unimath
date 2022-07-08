---
title: Equivalences between categories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.equivalences-categories where

open import category-theory.categories using (Cat; precat-Cat)
open import category-theory.equivalences-precategories using
  ( is-equiv-functor-Precat; equiv-Precat)
open import category-theory.functors-categories using (functor-Cat)
open import foundation.universe-levels using (UU; _⊔_)
```

## Idea

A functor `F : C → D` on categories is an equivalence if it is an equivalence on the underlying precategories.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Cat l1 l2)
  (D : Cat l3 l4) where

  is-equiv-functor-Cat : functor-Cat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Cat = is-equiv-functor-Precat (precat-Cat C) (precat-Cat D)

  equiv-Cat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Cat = equiv-Precat (precat-Cat C) (precat-Cat D)
```
