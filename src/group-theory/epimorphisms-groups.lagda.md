# Epimorphisms in groups

```agda
module group-theory.epimorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.epimorphisms-large-precategories

open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.precategory-of-groups
```

</details>

## Idea

A group homomorphism `f : x → y` is a epimorphism if whenever we have two group homomorphisms `g h : y → w` such that `g ∘ f = h ∘ f`, then in fact `g = h`. The way to state this in Homotopy Type Theory is to say that precomposition by `f` is an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : type-hom-Group G H)
  where

  is-epi-Group-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
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
