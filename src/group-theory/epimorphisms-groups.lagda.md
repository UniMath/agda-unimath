---
title: Epimorphisms in groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.epimorphisms-groups where

open import category-theory.epimorphisms-large-precategories using
  ( is-epi-Large-Precat-Prop; is-epi-iso-Large-Precat)

open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.groups using (Group)
open import group-theory.homomorphisms-groups using (type-hom-Group)
open import group-theory.isomorphisms-groups using (type-iso-Group; hom-iso-Group)
open import group-theory.precategory-of-groups using (Group-Large-Precat)
```

## Idea

A group homomorphism `f : x → y` is a epimorphism if whenever we have two group homomorphisms `g h : y → w` such that `g ∘ f = h ∘ f`, then in fact `g = h`. The way to state this in Homotopy Type Theory is to say that precomposition by `f` is an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : type-hom-Group G H)
  where

  is-epi-Group-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-epi-Group-Prop =
    is-epi-Large-Precat-Prop Group-Large-Precat l3 G H f

  is-epi-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-epi-Group = type-Prop is-epi-Group-Prop

  is-prop-is-epi-Group : is-prop is-epi-Group
  is-prop-is-epi-Group = is-prop-type-Prop is-epi-Group-Prop
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : type-iso-Group G H)
  where

  is-epi-iso-Group :
    is-epi-Group l3 G H (hom-iso-Group G H f)
  is-epi-iso-Group = is-epi-iso-Large-Precat Group-Large-Precat l3 G H f
```
