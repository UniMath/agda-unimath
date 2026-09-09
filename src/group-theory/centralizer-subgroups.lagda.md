# Centralizer subgroups

```agda
module group-theory.centralizer-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

Consider a [subset](group-theory.subsets-groups.md) `S` of a
[group](group-theory.groups.md) `G`. The **centralizer subgroup** `Cᴳ(S)` of `S`
is the subgroup of elements `g : G` such that `gs=sg` for every `s ∈ S`. In
other words, it consists of the elements of `G` that commute with all the
elements of `S`.

The definition of the centralizer is similar, but not identical to the
definition of the [normalizer](group-theory.normalizer-subgroups.md). There is
an inclusion of the centralizer into the normalizer, but not the other way
around. The centralizer should also not be confused with the
[center](group-theory.centers-groups.md) of a group.

## Definitions

```agda
module _
  {l1 l2 : Level} (G : Group l1) (S : subset-Group l2 G)
  where

  subset-centralizer-subset-Group : subset-Group (l1 ⊔ l2) G
  subset-centralizer-subset-Group x =
    Π-Prop
      ( type-Group G)
      ( λ y →
        hom-Prop (S y) (Id-Prop (set-Group G) (conjugation-Group G x y) y))

  is-in-centralizer-subset-Group : type-Group G → UU (l1 ⊔ l2)
  is-in-centralizer-subset-Group =
    is-in-subtype subset-centralizer-subset-Group

  contains-unit-centralizer-subset-Group :
    contains-unit-subset-Group G subset-centralizer-subset-Group
  contains-unit-centralizer-subset-Group y s =
    compute-conjugation-unit-Group G y

  is-closed-under-multiplication-centralizer-subset-Group :
    is-closed-under-multiplication-subset-Group G
      subset-centralizer-subset-Group
  is-closed-under-multiplication-centralizer-subset-Group {x} {y} u v z s =
    ( compute-conjugation-mul-Group G x y z) ∙
    ( ap (conjugation-Group G x) (v z s)) ∙
    ( u z s)

  is-closed-under-inverses-centralizer-subset-Group :
    is-closed-under-inverses-subset-Group G subset-centralizer-subset-Group
  is-closed-under-inverses-centralizer-subset-Group {x} u y s =
    transpose-eq-conjugation-inv-Group G (inv (u y s))

  centralizer-subset-Group : Subgroup (l1 ⊔ l2) G
  pr1 centralizer-subset-Group =
    subset-centralizer-subset-Group
  pr1 (pr2 centralizer-subset-Group) =
    contains-unit-centralizer-subset-Group
  pr1 (pr2 (pr2 centralizer-subset-Group)) =
    is-closed-under-multiplication-centralizer-subset-Group
  pr2 (pr2 (pr2 centralizer-subset-Group)) =
    is-closed-under-inverses-centralizer-subset-Group
```
