# Isomorphisms in categories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.isomorphisms-categories where

open import categories.categories using
  ( Cat; obj-Cat; type-hom-Cat; precat-Cat)
open import categories.isomorphisms-precategories using
  ( is-iso-Precat)
open import foundation.universe-levels using (UU; Level)
```

## Idea

An isomorphism in a category is an isomorphism in the underlying precategory.

## Definition

```agda
is-iso-Cat :
  {l1 l2 : Level} (C : Cat l1 l2) →
  {x y : obj-Cat C} (f : type-hom-Cat C x y) → UU l2
is-iso-Cat C = is-iso-Precat (precat-Cat C)
```
