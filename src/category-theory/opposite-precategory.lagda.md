---
title: The opposite precategory
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.opposite-precategory where

open import foundation.dependent-pair-types
open import foundation.identity-types

open import category-theory.precategories
```

```agda
module _ {i j} (C : Precat i j) where

  op : Precat i j
  pr1 op = obj-Precat C
  pr1 (pr2 op) x y = hom-Precat C y x
  pr1 (pr1 (pr2 (pr2 op))) g f = comp-hom-Precat C f g
  pr2 (pr1 (pr2 (pr2 op))) h g f = inv (assoc-comp-hom-Precat C f g h)
  pr1 (pr2 (pr2 (pr2 op))) x = id-hom-Precat C
  pr1 (pr2 (pr2 (pr2 (pr2 op)))) f = right-unit-law-comp-hom-Precat C f
  pr2 (pr2 (pr2 (pr2 (pr2 op)))) f = left-unit-law-comp-hom-Precat C f
```
