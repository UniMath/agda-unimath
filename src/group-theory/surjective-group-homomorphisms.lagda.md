# Surjective group homomorphisms

```agda
module group-theory.surjective-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.full-subgroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.surjective-semigroup-homomorphisms
```

</details>

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` is said
to be **surjective** if its underlying map is
[surjective](foundation.surjective-maps.md).

## Definition

### Surjective group homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-surjective-prop-hom-Group : Prop (l1 ⊔ l2)
  is-surjective-prop-hom-Group =
    is-surjective-prop-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-surjective-hom-Group : UU (l1 ⊔ l2)
  is-surjective-hom-Group =
    is-surjective-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-prop-is-surjective-hom-Group : is-prop is-surjective-hom-Group
  is-prop-is-surjective-hom-Group =
    is-prop-is-surjective-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
```

## Properties

### A group homomorphism is surjective if and only if its image is the full subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-surjective-is-full-subgroup-image-hom-Group :
    is-full-Subgroup H (image-hom-Group G H f) →
    is-surjective-hom-Group G H f
  is-surjective-is-full-subgroup-image-hom-Group u = u

  is-full-subgroup-image-is-surjective-hom-Group :
    is-surjective-hom-Group G H f →
    is-full-Subgroup H (image-hom-Group G H f)
  is-full-subgroup-image-is-surjective-hom-Group u = u
```
