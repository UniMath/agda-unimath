# Intersections of subgroups of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.intersections-subgroups-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes funext
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.intersections-subgroups-groups funext
open import group-theory.subgroups-abelian-groups funext
```

</details>

## Idea

The **intersection** of two
[subgroups](group-theory.subgroups-abelian-groups.md) of an
[abelian group](group-theory.abelian-groups.md) `A` consists of the elements
contained in both subgroups.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A) (C : Subgroup-Ab l3 A)
  where

  intersection-Subgroup-Ab : Subgroup-Ab (l2 ⊔ l3) A
  intersection-Subgroup-Ab = intersection-Subgroup (group-Ab A) B C

  subset-intersection-Subgroup-Ab : subtype (l2 ⊔ l3) (type-Ab A)
  subset-intersection-Subgroup-Ab =
    subset-intersection-Subgroup (group-Ab A) B C

  is-in-intersection-Subgroup-Ab : type-Ab A → UU (l2 ⊔ l3)
  is-in-intersection-Subgroup-Ab =
    is-in-intersection-Subgroup (group-Ab A) B C

  contains-zero-intersection-Subgroup-Ab :
    contains-zero-subset-Ab A subset-intersection-Subgroup-Ab
  contains-zero-intersection-Subgroup-Ab =
    contains-unit-intersection-Subgroup (group-Ab A) B C

  is-closed-under-addition-intersection-Subgroup-Ab :
    is-closed-under-addition-subset-Ab A subset-intersection-Subgroup-Ab
  is-closed-under-addition-intersection-Subgroup-Ab =
    is-closed-under-multiplication-intersection-Subgroup (group-Ab A) B C

  is-closed-under-negatives-intersection-Subgroup-Ab :
    is-closed-under-negatives-subset-Ab A subset-intersection-Subgroup-Ab
  is-closed-under-negatives-intersection-Subgroup-Ab =
    is-closed-under-inverses-intersection-Subgroup (group-Ab A) B C

  is-subgroup-intersection-Subgroup-Ab :
    is-subgroup-Ab A subset-intersection-Subgroup-Ab
  is-subgroup-intersection-Subgroup-Ab =
    is-subgroup-intersection-Subgroup (group-Ab A) B C
```
