# Images of group homomorphisms

```agda
module group-theory.images-of-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universal-property-image
open import foundation.universe-levels

open import group-theory.full-subgroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.subgroups
open import group-theory.subsets-groups
open import group-theory.surjective-group-homomorphisms
```

</details>

## Idea

The [image](foundation.images.md) of a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` contains
the unit element and is closed under multiplication and inverses. It is
therefore a [subgroup](group-theory.subgroups.md) of the
[group](group-theory.groups.md) `H`. Alternatively, it can be described as the
least subgroup of `H` that contains all the values of `f`.

## Definitions

### The universal property of the image of a group homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  (K : Subgroup l3 H)
  where

  is-image-hom-Group : UUω
  is-image-hom-Group =
    {l : Level} (L : Subgroup l H) →
    leq-Subgroup H K L ↔
    ((g : type-Group G) → is-in-Subgroup H L (map-hom-Group G H f g))
```

### The image subgroup of a group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  where

  subset-image-hom-Group : subset-Group (l1 ⊔ l2) H
  subset-image-hom-Group = subtype-im (map-hom-Group G H f)

  is-image-subtype-subset-image-hom-Group :
    is-image-subtype (map-hom-Group G H f) subset-image-hom-Group
  is-image-subtype-subset-image-hom-Group =
    is-image-subtype-subtype-im (map-hom-Group G H f)

  abstract
    contains-unit-image-hom-Group :
      contains-unit-subset-Group H subset-image-hom-Group
    contains-unit-image-hom-Group =
      unit-trunc-Prop (unit-Group G , preserves-unit-hom-Group G H f)

  abstract
    is-closed-under-multiplication-image-hom-Group :
      is-closed-under-multiplication-subset-Group H subset-image-hom-Group
    is-closed-under-multiplication-image-hom-Group x y K L =
      apply-twice-universal-property-trunc-Prop K L
        ( subset-image-hom-Group (mul-Group H x y))
        ( λ { (g , refl) (h , refl) →
              unit-trunc-Prop
                ( mul-Group G g h , preserves-mul-hom-Group G H f g h)})

  abstract
    is-closed-under-inv-image-hom-Group :
      is-closed-under-inv-subset-Group H subset-image-hom-Group
    is-closed-under-inv-image-hom-Group x K =
      apply-universal-property-trunc-Prop K
        ( subset-image-hom-Group (inv-Group H x))
        ( λ { (g , refl) →
              unit-trunc-Prop
                ( inv-Group G g , preserves-inv-hom-Group G H f g)})

  is-subgroup-image-hom-Group :
    is-subgroup-subset-Group H subset-image-hom-Group
  pr1 is-subgroup-image-hom-Group =
    contains-unit-image-hom-Group
  pr1 (pr2 is-subgroup-image-hom-Group) =
    is-closed-under-multiplication-image-hom-Group
  pr2 (pr2 is-subgroup-image-hom-Group) =
    is-closed-under-inv-image-hom-Group

  image-hom-Group : Subgroup (l1 ⊔ l2) H
  pr1 image-hom-Group = subset-image-hom-Group
  pr2 image-hom-Group = is-subgroup-image-hom-Group

  is-image-image-hom-Group :
    is-image-hom-Group G H f image-hom-Group
  is-image-image-hom-Group K =
    is-image-subtype-subset-image-hom-Group (subset-Subgroup H K)

  contains-values-image-hom-Group :
    (g : type-Group G) →
    is-in-Subgroup H image-hom-Group (map-hom-Group G H f g)
  contains-values-image-hom-Group =
    forward-implication
      ( is-image-image-hom-Group image-hom-Group)
      ( refl-leq-Subgroup H image-hom-Group)

  leq-image-hom-Group :
    {l : Level} (K : Subgroup l H) →
    ((g : type-Group G) → is-in-Subgroup H K (map-hom-Group G H f g)) →
    leq-Subgroup H image-hom-Group K
  leq-image-hom-Group K =
    backward-implication (is-image-image-hom-Group K)
```

## Properties

### A group homomorphism is surjective if and only if its image is the full subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
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
