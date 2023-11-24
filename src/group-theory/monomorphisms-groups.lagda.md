# Monomorphisms in the category of groups

```agda
module group-theory.monomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.monomorphisms-in-large-precategories

open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.precategory-of-groups
```

</details>

## Idea

A group homomorphism `f : x → y` is a monomorphism if whenever we have two group
homomorphisms `g h : w → x` such that `f ∘ g = f ∘ h`, then in fact `g = h`. The
way to state this in Homotopy Type Theory is to say that postcomposition by `f`
is an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : hom-Group G H)
  where

  is-mono-prop-hom-Group : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-prop-hom-Group =
    is-mono-prop-Large-Precategory Group-Large-Precategory l3 G H f

  is-mono-hom-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Group = type-Prop is-mono-prop-hom-Group

  is-prop-is-mono-hom-Group : is-prop is-mono-hom-Group
  is-prop-is-mono-hom-Group = is-prop-type-Prop is-mono-prop-hom-Group
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : iso-Group G H)
  where

  is-mono-iso-Group : is-mono-hom-Group l3 G H (hom-iso-Group G H f)
  is-mono-iso-Group =
    is-mono-iso-Large-Precategory Group-Large-Precategory l3 G H f
```
