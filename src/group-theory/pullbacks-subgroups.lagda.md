# Pullbacks of subgroups

```agda
module group-theory.pullbacks-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.pullbacks-subsemigroups
open import group-theory.subgroups
open import group-theory.subsemigroups
open import group-theory.subsets-groups

open import order-theory.commuting-squares-of-order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-order-preserving-maps-large-posets
```

</details>

## Idea

Given a [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H`
into a [group](group-theory.groups.md) `H` equipped with a
[subgroup](group-theory.subgroups.md) `K ≤ H`, the **pullback** `pullback f K`
of `K` along `f` is defined by substituting `f` in `K`. In other words, it is
the subgroup `pullback f K` of `G` consisting of the elements `x : G` such that
`f x ∈ K`.

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

### The order preserving map `pullback-Subgroup`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-order-pullback-Subgroup :
    {l3 l4 : Level} (S : Subgroup l3 H) (T : Subgroup l4 H) →
    leq-Subgroup H S T →
    leq-Subgroup G (pullback-Subgroup G H f S) (pullback-Subgroup G H f T)
  preserves-order-pullback-Subgroup S T =
    preserves-order-pullback-Subsemigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
      ( subsemigroup-Subgroup H S)
      ( subsemigroup-Subgroup H T)

  pullback-subgroup-hom-large-poset-hom-Group :
    hom-Large-Poset (λ l → l) (Subgroup-Large-Poset H) (Subgroup-Large-Poset G)
  map-hom-Large-Preorder pullback-subgroup-hom-large-poset-hom-Group =
    pullback-Subgroup G H f
  preserves-order-hom-Large-Preorder
    pullback-subgroup-hom-large-poset-hom-Group =
    preserves-order-pullback-Subgroup
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                   pullback f
     Subgroup H ----------------> Subgroup G
         |                            |
  K ↦ UK |                            | K ↦ UK
         |                            |
         ∨                            ∨
   subset-Group H ------------> subset-Group G
                   pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  coherence-square-pullback-subset-Subgroup :
    coherence-square-hom-Large-Poset
      ( Subgroup-Large-Poset H)
      ( powerset-Large-Poset (type-Group H))
      ( Subgroup-Large-Poset G)
      ( powerset-Large-Poset (type-Group G))
      ( pullback-subgroup-hom-large-poset-hom-Group G H f)
      ( subset-subgroup-hom-large-poset-Group H)
      ( subset-subgroup-hom-large-poset-Group G)
      ( pullback-subtype-hom-Large-Poset (map-hom-Group G H f))
  coherence-square-pullback-subset-Subgroup =
    refl-sim-hom-Large-Poset
      ( Subgroup-Large-Poset H)
      ( powerset-Large-Poset (type-Group G))
      ( comp-hom-Large-Poset
        ( Subgroup-Large-Poset H)
        ( Subgroup-Large-Poset G)
        ( powerset-Large-Poset (type-Group G))
        ( subset-subgroup-hom-large-poset-Group G)
        ( pullback-subgroup-hom-large-poset-hom-Group G H f))
```

### Pullbacks of normal subgroups are normal

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (N : Normal-Subgroup l3 H)
  where

  subgroup-pullback-Normal-Subgroup : Subgroup l3 G
  subgroup-pullback-Normal-Subgroup =
    pullback-Subgroup G H f (subgroup-Normal-Subgroup H N)

  is-normal-pullback-Normal-Subgroup :
    is-normal-Subgroup G subgroup-pullback-Normal-Subgroup
  is-normal-pullback-Normal-Subgroup x (y , n) =
    is-closed-under-eq-Normal-Subgroup' H N
      ( is-normal-Normal-Subgroup H N
        ( map-hom-Group G H f x)
        ( map-hom-Group G H f y)
        ( n))
      ( preserves-conjugation-hom-Group G H f)

  pullback-Normal-Subgroup : Normal-Subgroup l3 G
  pr1 pullback-Normal-Subgroup = subgroup-pullback-Normal-Subgroup
  pr2 pullback-Normal-Subgroup = is-normal-pullback-Normal-Subgroup
```
