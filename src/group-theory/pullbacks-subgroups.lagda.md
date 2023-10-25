# Pullbacks of subgroups

```agda
module group-theory.pullbacks-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.pullbacks-subsemigroups
open import group-theory.subgroups
open import group-theory.subsemigroups
open import group-theory.subsets-groups
```

</details>

## Idea

Given a [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H`
into a [group](group-theory.groups.md) `H` equipped with a
[subgroup](group-theory.subgroups.md) `K ≤ H`, the **pullback** `f∗K` of `K`
along `f` is defined by substituting `f` in `K`. In other words, it is the
subgroup `f∗K` of `G` consisting of the elements `x : G` such that `f x ∈ K`.

## Definitions

### Pullbacks of subgroups

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (K : Subgroup l3 H)
  where

  subsemigroup-pullback-Subgroup : Subsemigroup l3 (semigroup-Group G)
  subsemigroup-pullback-Subgroup =
    pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  subset-pullback-Subgroup : subset-Group l3 G
  subset-pullback-Subgroup =
    subset-pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  is-in-pullback-Subgroup : type-Group G → UU l3
  is-in-pullback-Subgroup =
    is-in-pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  is-closed-under-eq-pullback-Subgroup :
    {x y : type-Group G} →
    is-in-pullback-Subgroup x → x ＝ y → is-in-pullback-Subgroup y
  is-closed-under-eq-pullback-Subgroup =
    is-closed-under-eq-pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  is-closed-under-eq-pullback-Subgroup' :
    {x y : type-Group G} →
    is-in-pullback-Subgroup y → x ＝ y → is-in-pullback-Subgroup x
  is-closed-under-eq-pullback-Subgroup' =
    is-closed-under-eq-pullback-Subsemigroup'
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  contains-unit-pullback-Subgroup :
    contains-unit-subset-Group G subset-pullback-Subgroup
  contains-unit-pullback-Subgroup =
    is-closed-under-eq-Subgroup' H K
      ( contains-unit-Subgroup H K)
      ( preserves-unit-hom-Group G H f)

  is-closed-under-multiplication-pullback-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-pullback-Subgroup
  is-closed-under-multiplication-pullback-Subgroup =
    is-closed-under-multiplication-pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H K)

  is-closed-under-inverses-pullback-Subgroup :
    is-closed-under-inverses-subset-Group G subset-pullback-Subgroup
  is-closed-under-inverses-pullback-Subgroup p =
    is-closed-under-eq-Subgroup' H K
      ( is-closed-under-inverses-Subgroup H K p)
      ( preserves-inv-hom-Group G H f)

  is-subgroup-pullback-Subgroup :
    is-subgroup-subset-Group G subset-pullback-Subgroup
  pr1 is-subgroup-pullback-Subgroup =
    contains-unit-pullback-Subgroup
  pr1 (pr2 is-subgroup-pullback-Subgroup) =
    is-closed-under-multiplication-pullback-Subgroup
  pr2 (pr2 is-subgroup-pullback-Subgroup) =
    is-closed-under-inverses-pullback-Subgroup

  pullback-Subgroup : Subgroup l3 G
  pr1 pullback-Subgroup = subset-pullback-Subgroup
  pr2 pullback-Subgroup = is-subgroup-pullback-Subgroup
```
