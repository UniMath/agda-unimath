# Kernels of homomorphisms between abelian groups

```agda
module group-theory.kernels-homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.embeddings-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups-abelian-groups
open import group-theory.subsets-abelian-groups
```

</details>

## Idea

The
{{#concept "kernel" Disambiguation="of a homomorphism of abelian groups" Agda=kernel-hom-Ab}}
of a [group homomorphism](group-theory.homomorphisms-abelian-groups.md)
`f : A → B` between [abelian groups](group-theory.abelian-groups.md) `A` and `B`
is the [subgroup](group-theory.subgroups-abelian-groups.md) of `A` consisting of
those elements `x : A` such that `f x ＝ zero-Ab B`.

## Definitions

### Kernels of group homomorphisms between abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B)
  where

  subset-kernel-hom-Ab : subset-Ab l2 A
  subset-kernel-hom-Ab =
    subset-kernel-hom-Group (group-Ab A) (group-Ab B) f

  is-in-kernel-hom-Ab : type-Ab A → UU l2
  is-in-kernel-hom-Ab =
    is-in-kernel-hom-Group (group-Ab A) (group-Ab B) f

  contains-zero-subset-kernel-hom-Ab :
    is-in-kernel-hom-Ab (zero-Ab A)
  contains-zero-subset-kernel-hom-Ab =
    contains-unit-subset-kernel-hom-Group (group-Ab A) (group-Ab B) f

  is-closed-under-addition-subset-kernel-hom-Ab :
    is-closed-under-addition-subset-Ab A subset-kernel-hom-Ab
  is-closed-under-addition-subset-kernel-hom-Ab =
    is-closed-under-multiplication-subset-kernel-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)

  is-closed-under-negatives-subset-kernel-hom-Ab :
    is-closed-under-negatives-subset-Ab A subset-kernel-hom-Ab
  is-closed-under-negatives-subset-kernel-hom-Ab =
    is-closed-under-inverses-subset-kernel-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)

  kernel-hom-Ab : Subgroup-Ab l2 A
  kernel-hom-Ab =
    subgroup-kernel-hom-Group (group-Ab A) (group-Ab B) f

  ab-kernel-hom-Ab : Ab (l1 ⊔ l2)
  ab-kernel-hom-Ab = ab-Subgroup-Ab A kernel-hom-Ab

  inclusion-kernel-hom-Ab : hom-Ab ab-kernel-hom-Ab A
  inclusion-kernel-hom-Ab =
    inclusion-kernel-hom-Group (group-Ab A) (group-Ab B) f

  is-emb-inclusion-kernel-hom-Ab :
    is-emb-hom-Ab ab-kernel-hom-Ab A inclusion-kernel-hom-Ab
  is-emb-inclusion-kernel-hom-Ab =
    is-emb-inclusion-kernel-hom-Group (group-Ab A) (group-Ab B) f

  emb-inclusion-kernel-hom-Ab : emb-Ab ab-kernel-hom-Ab A
  emb-inclusion-kernel-hom-Ab =
    emb-inclusion-kernel-hom-Group (group-Ab A) (group-Ab B) f
```
