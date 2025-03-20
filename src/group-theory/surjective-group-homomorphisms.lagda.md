# Surjective group homomorphisms

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.surjective-group-homomorphisms
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions funext
open import foundation.surjective-maps funext
open import foundation.universe-levels

open import group-theory.full-subgroups funext
open import group-theory.groups funext
open import group-theory.homomorphisms-groups funext
open import group-theory.images-of-group-homomorphisms funext
open import group-theory.surjective-semigroup-homomorphisms funext
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
