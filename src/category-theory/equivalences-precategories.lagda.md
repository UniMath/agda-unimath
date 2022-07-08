---
title: Equivalences between precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.equivalences-precategories where

open import category-theory.functors-precategories using
  ( functor-Precat; comp-functor-Precat; id-functor-Precat)
open import category-theory.natural-isomorphisms-precategories using
  ( nat-iso-Precat)
open import category-theory.precategories using (Precat)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import foundation.universe-levels using (UU; _⊔_)
```

## Idea

A functor `F : C → D` is an equivalence of categories if there is a functor `G : D → C` such that:
- `comp G F` is naturally isomorphic to the identity functor on `C`,
- `comp F G` is naturally isomorphic to the identity functor on `D`.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Precat l1 l2)
  (D : Precat l3 l4) where

  is-equiv-functor-Precat : functor-Precat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Precat F =
    Σ ( functor-Precat D C)
      ( λ G →
        ( nat-iso-Precat C C
          ( comp-functor-Precat C D C G F)
          ( id-functor-Precat C)) ×
        ( nat-iso-Precat D D
          ( comp-functor-Precat D C D F G)
          ( id-functor-Precat D)))

  equiv-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Precat = Σ (functor-Precat C D) is-equiv-functor-Precat
```
