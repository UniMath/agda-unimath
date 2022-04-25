# Monomorphisms in groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.monomorphisms-groups where

open import category-theory.monomorphisms-large-precategories using
  ( is-mono-Large-Precat-Prop; is-mono-iso-Large-Precat)

open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.groups using (Group)
open import group-theory.homomorphisms-groups using (type-hom-Group)
open import group-theory.isomorphisms-groups using (type-iso-Group; hom-iso-Group)
open import group-theory.precategory-of-groups using (Group-Large-Precat)
```

## Idea

A group homomorphism `f : x → y` is a monomorphism if whenever we have two group homomorphisms `g h : w → x` such that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state this in Homotopy Type Theory is to say that postcomposition by `f` is an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : type-hom-Group G H)
  where

  is-mono-Group-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Group-Prop =
    is-mono-Large-Precat-Prop Group-Large-Precat l3 G H f

  is-mono-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Group = type-Prop is-mono-Group-Prop

  is-prop-is-mono-Group : is-prop is-mono-Group
  is-prop-is-mono-Group = is-prop-type-Prop is-mono-Group-Prop
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : type-iso-Group G H)
  where

  is-mono-iso-Group :
    is-mono-Group l3 G H (hom-iso-Group G H f)
  is-mono-iso-Group = is-mono-iso-Large-Precat Group-Large-Precat l3 G H f
```
