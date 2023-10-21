# Functoriality of quotient groups

```agda
module group-theory.functoriality-quotient-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commuting-squares-of-group-homomorphisms
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-groups-equipped-with-normal-subgroups
open import group-theory.normal-subgroups
open import group-theory.nullifying-group-homomorphisms
open import group-theory.quotient-groups
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
    V          V
   G/N -----> H/M
         g
```

[commutes](group-theory.commuting-squares-of-group-homomorphisms.md).

## Definitions

### The quotient functor on groups

#### The functoriality of quotient groups

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : hom-Group G H)
  (P : reflects-normal-subgroup-hom-Group G H N M f)
  where

  abstract
    unique-hom-quotient-Group :
      is-contr
        ( Σ ( hom-Group (quotient-Group G N) (quotient-Group H M))
            ( coherence-square-hom-Group G H
              ( quotient-Group G N)
              ( quotient-Group H M)
              ( f)
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
          ( f , P))

  abstract
    hom-quotient-Group : hom-Group (quotient-Group G N) (quotient-Group H M)
    hom-quotient-Group = pr1 (center unique-hom-quotient-Group)

    naturality-hom-quotient-Group :
      coherence-square-hom-Group G H
        ( quotient-Group G N)
        ( quotient-Group H M)
        ( f)
        ( quotient-hom-Group G N)
        ( quotient-hom-Group H M)
        ( hom-quotient-Group)
    naturality-hom-quotient-Group =
      pr2 (center unique-hom-quotient-Group)
```
