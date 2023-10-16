# Functoriality of quotient groups

```agda
module group-theory.functoriality-quotient-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

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
  (f : hom-Group G H)
  where

  reflects-normal-subgroup-hom-Group : UU (l1 ⊔ l3 ⊔ l4)
  reflects-normal-subgroup-hom-Group =
    (x : type-Group G) → is-in-Normal-Subgroup G N x →
    is-in-Normal-Subgroup H M (map-hom-Group G H f x)
```

### The functoriality of the quotient groups

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : hom-Group G H)
  (P : reflects-normal-subgroup-hom-Group G H N M f)
  where

  hom-quotient-Group : hom-Group (quotient-Group G N) (quotient-Group H M)
  hom-quotient-Group = {!!}
```
