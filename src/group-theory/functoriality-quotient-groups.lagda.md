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
open import group-theory.normal-subgroups
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

### The property of group homomorphisms of reflecting a normal subgroup

We say that a group homomorphism `f : G → H` **reflects** a normal subgroup `N`
of `G` into a normal subgroup `M` of `H` if the property

```text
  x ∈ N ⇒ f x ∈ M
```

holds for every `x : G`, i.e., if `f` maps elements in `N` to elements in `M`.

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  where

  reflects-normal-subgroup-hom-Group : hom-Group G H → UU (l1 ⊔ l3 ⊔ l4)
  reflects-normal-subgroup-hom-Group f =
    (x : type-Group G) → is-in-Normal-Subgroup G N x →
    is-in-Normal-Subgroup H M (map-hom-Group G H f x)

  reflecting-hom-Group : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  reflecting-hom-Group = Σ (hom-Group G H) reflects-normal-subgroup-hom-Group

module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : reflecting-hom-Group G H N M)
  where

  hom-reflecting-hom-Group : hom-Group G H
  hom-reflecting-hom-Group = pr1 f

  reflects-normal-subgroup-reflecting-hom-Group :
    reflects-normal-subgroup-hom-Group G H N M hom-reflecting-hom-Group
  reflects-normal-subgroup-reflecting-hom-Group = pr2 f

  map-reflecting-hom-Group : type-Group G → type-Group H
  map-reflecting-hom-Group = map-hom-Group G H hom-reflecting-hom-Group
```

### Composition of nullifying homomorphisms and reflecting homomorphisms

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3)
  (N : Normal-Subgroup l4 G) (M : Normal-Subgroup l5 H)
  where

  hom-comp-nullifying-hom-reflecting-hom-Group :
    nullifying-hom-Group H K M →
    reflecting-hom-Group G H N M →
    hom-Group G K
  hom-comp-nullifying-hom-reflecting-hom-Group g f =
    comp-hom-Group G H K
      ( hom-nullifying-hom-Group H K M g)
      ( hom-reflecting-hom-Group G H N M f)

  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group :
    ( g : nullifying-hom-Group H K M)
    ( f : reflecting-hom-Group G H N M) →
    nullifies-normal-subgroup-hom-Group G K
      ( hom-comp-nullifying-hom-reflecting-hom-Group g f)
      ( N)
  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group g f x n =
    nullifies-nullifying-hom-Group H K M g
      ( map-reflecting-hom-Group G H N M f x)
      ( reflects-normal-subgroup-reflecting-hom-Group G H N M f x n)

  comp-nullifying-hom-reflecting-hom-Group :
    nullifying-hom-Group H K M →
    reflecting-hom-Group G H N M →
    nullifying-hom-Group G K N
  pr1 (comp-nullifying-hom-reflecting-hom-Group g f) =
    hom-comp-nullifying-hom-reflecting-hom-Group g f
  pr2 (comp-nullifying-hom-reflecting-hom-Group g f) =
    nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group g f
```

### The functoriality of the quotient groups

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
