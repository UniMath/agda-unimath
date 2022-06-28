---
title: Isomorphisms in categories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.isomorphisms-categories where

open import category-theory.categories using
  ( Cat; obj-Cat; type-hom-Cat; precat-Cat; id-hom-Cat)
open import category-theory.isomorphisms-precategories using
  ( is-iso-Precat; iso-Precat; is-prop-is-iso-Precat;
    is-set-iso-Precat; iso-Precat-Set; is-iso-id-hom-Precat;
    id-iso-Precat; iso-eq-Precat)
open import foundation.identity-types using (_＝_)
open import foundation.propositions using (is-prop)
open import foundation.sets using (is-set; UU-Set)
open import foundation.universe-levels using (UU; Level)
```

## Idea

An isomorphism in a category is an isomorphism in the underlying precategory.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-iso-Cat : {x y : obj-Cat C} (f : type-hom-Cat C x y) → UU l2
  is-iso-Cat = is-iso-Precat (precat-Cat C)

  iso-Cat : (x y : obj-Cat C) → UU l2
  iso-Cat = iso-Precat (precat-Cat C)
```

## Examples

### The identity morphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-iso-id-hom-Cat : {x : obj-Cat C} → is-iso-Cat C (id-hom-Cat C {x})
  is-iso-id-hom-Cat = is-iso-id-hom-Precat (precat-Cat C)

  id-iso-Cat : {x : obj-Cat C} → iso-Cat C x x
  id-iso-Cat = id-iso-Precat (precat-Cat C)
```

### Equalities give rise to isomorphisms

```agda
iso-eq-Cat :
  {l1 l2 : Level} (C : Cat l1 l2) →
  (x y : obj-Cat C) → x ＝ y → iso-Cat C x y
iso-eq-Cat C = iso-eq-Precat (precat-Cat C)
```

## Properties

### The property of being an isomorphism is a proposition

```agda
is-prop-is-iso-Cat :
  {l1 l2 : Level} (C : Cat l1 l2) →
  {x y : obj-Cat C} (f : type-hom-Cat C x y) → is-prop (is-iso-Cat C f)
is-prop-is-iso-Cat C = is-prop-is-iso-Precat (precat-Cat C)
```

### The type of isomorphisms forms a set

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-set-iso-Cat : (x y : obj-Cat C) → is-set (iso-Cat C x y)
  is-set-iso-Cat = is-set-iso-Precat (precat-Cat C)

  iso-Cat-Set : (x y : obj-Cat C) → UU-Set l2
  iso-Cat-Set = iso-Precat-Set (precat-Cat C)
```
