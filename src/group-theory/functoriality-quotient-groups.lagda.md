# Functoriality of quotient groups

```agda
{-# OPTIONS --lossy-unification #-}

open import foundation.function-extensionality-axiom

module
  group-theory.functoriality-quotient-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.commuting-squares-of-group-homomorphisms funext
open import group-theory.groups funext
open import group-theory.homomorphisms-groups funext
open import group-theory.homomorphisms-groups funext-equipped-with-normal-subgroups
open import group-theory.normal-subgroups funext
open import group-theory.nullifying-group-homomorphisms funext
open import group-theory.quotient-groups funext
```

</details>

## Idea

Consider a [normal subgroup](group-theory.normal-subgroups.md) `N` of a
[group](group-theory.groups.md) `G` and a normal subgroup `M` of a group `H`.
Then any [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H`
satisfying the property that `x ∈ N ⇒ f x ∈ M` induces a group homomorphism
`g : G/N → H/M`, which is the unique group homomorphism such that the square

```text
         f
    G -------> H
    |          |
  q |          | q
    ∨          ∨
   G/N -----> H/M
         g
```

[commutes](group-theory.commuting-squares-of-group-homomorphisms.md).

## Definitions

### The quotient functor on groups

#### The functorial action of the quotient group construction

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : reflecting-hom-Group G H N M)
  where

  abstract
    unique-hom-quotient-Group :
      is-contr
        ( Σ ( hom-Group (quotient-Group G N) (quotient-Group H M))
            ( coherence-square-hom-Group G H
              ( quotient-Group G N)
              ( quotient-Group H M)
              ( hom-reflecting-hom-Group G H N M f)
              ( quotient-hom-Group G N)
              ( quotient-hom-Group H M)))
    unique-hom-quotient-Group =
      unique-mapping-property-quotient-Group G N
        ( quotient-Group H M)
        ( comp-nullifying-hom-reflecting-hom-Group G H
          ( quotient-Group H M)
          ( N)
          ( M)
          ( nullifying-quotient-hom-Group H M)
          ( f))

  abstract
    hom-quotient-Group : hom-Group (quotient-Group G N) (quotient-Group H M)
    hom-quotient-Group = pr1 (center unique-hom-quotient-Group)

    naturality-hom-quotient-Group :
      coherence-square-hom-Group G H
        ( quotient-Group G N)
        ( quotient-Group H M)
        ( hom-reflecting-hom-Group G H N M f)
        ( quotient-hom-Group G N)
        ( quotient-hom-Group H M)
        ( hom-quotient-Group)
    naturality-hom-quotient-Group =
      pr2 (center unique-hom-quotient-Group)

  map-hom-quotient-Group : type-quotient-Group G N → type-quotient-Group H M
  map-hom-quotient-Group =
    map-hom-Group (quotient-Group G N) (quotient-Group H M) hom-quotient-Group
```

#### The functorial action preserves the identity homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    preserves-id-hom-quotient-Group' :
      (p : reflects-normal-subgroup-hom-Group G G N N (id-hom-Group G)) →
      hom-quotient-Group G G N N (id-reflecting-hom-Group' G N p) ＝
      id-hom-Group (quotient-Group G N)
    preserves-id-hom-quotient-Group' p =
      ap
        ( pr1)
        ( eq-is-contr'
          ( unique-mapping-property-quotient-Group G N
            ( quotient-Group G N)
            ( nullifying-quotient-hom-Group G N))
          ( hom-quotient-Group G G N N (id-reflecting-hom-Group' G N p) ,
            naturality-hom-quotient-Group G G N N
              ( id-reflecting-hom-Group' G N p))
          ( id-hom-Group (quotient-Group G N) ,
            refl-htpy))

  abstract
    preserves-id-hom-quotient-Group :
      hom-quotient-Group G G N N (id-reflecting-hom-Group G N) ＝
      id-hom-Group (quotient-Group G N)
    preserves-id-hom-quotient-Group =
      preserves-id-hom-quotient-Group'
        ( reflects-normal-subgroup-id-hom-Group G N)
```

#### The functorial action preserves composition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3)
  (L : Normal-Subgroup l4 G)
  (M : Normal-Subgroup l5 H)
  (N : Normal-Subgroup l6 K)
  where

  abstract
    preserves-comp-hom-quotient-Group' :
      (g : reflecting-hom-Group H K M N)
      (f : reflecting-hom-Group G H L M)
      (p :
        reflects-normal-subgroup-hom-Group G K L N
          ( hom-comp-reflecting-hom-Group G H K L M N g f)) →
      hom-quotient-Group G K L N
        ( comp-reflecting-hom-Group' G H K L M N g f p) ＝
      comp-hom-Group
        ( quotient-Group G L)
        ( quotient-Group H M)
        ( quotient-Group K N)
        ( hom-quotient-Group H K M N g)
        ( hom-quotient-Group G H L M f)
    preserves-comp-hom-quotient-Group' g f p =
      ap
        ( pr1)
        ( eq-is-contr'
          ( unique-mapping-property-quotient-Group G L
            ( quotient-Group K N)
            ( comp-nullifying-hom-reflecting-hom-Group G K
              ( quotient-Group K N)
              ( L)
              ( N)
              ( nullifying-quotient-hom-Group K N)
              ( comp-reflecting-hom-Group' G H K L M N g f p)))
          ( ( hom-quotient-Group G K L N
              ( comp-reflecting-hom-Group' G H K L M N g f p)) ,
            ( naturality-hom-quotient-Group G K L N
              ( comp-reflecting-hom-Group' G H K L M N g f p)))
          ( comp-hom-Group
            ( quotient-Group G L)
            ( quotient-Group H M)
            ( quotient-Group K N)
            ( hom-quotient-Group H K M N g)
            ( hom-quotient-Group G H L M f) ,
            ( pasting-horizontal-coherence-square-maps
              ( map-reflecting-hom-Group G H L M f)
              ( map-reflecting-hom-Group H K M N g)
              ( map-quotient-hom-Group G L)
              ( map-quotient-hom-Group H M)
              ( map-quotient-hom-Group K N)
              ( map-hom-quotient-Group G H L M f)
              ( map-hom-quotient-Group H K M N g)
              ( naturality-hom-quotient-Group G H L M f)
              ( naturality-hom-quotient-Group H K M N g))))

  abstract
    preserves-comp-hom-quotient-Group :
      (g : reflecting-hom-Group H K M N)
      (f : reflecting-hom-Group G H L M) →
      hom-quotient-Group G K L N (comp-reflecting-hom-Group G H K L M N g f) ＝
      comp-hom-Group
        ( quotient-Group G L)
        ( quotient-Group H M)
        ( quotient-Group K N)
        ( hom-quotient-Group H K M N g)
        ( hom-quotient-Group G H L M f)
    preserves-comp-hom-quotient-Group g f =
      preserves-comp-hom-quotient-Group' g f
        ( reflects-normal-subgroup-comp-reflecting-hom-Group G H K L M N g f)
```

#### The quotient group functor

This functor remains to be formalized.
