# Perfect groups

```agda
module group-theory.perfect-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commutator-subgroups
open import group-theory.full-subgroups
open import group-theory.groups
```

</details>

## Idea

A [group](group-theory.groups.md) `G` is said to be **perfect** if its
[commutator subgroup](group-theory.commutator-subgroups.md) is a
[full](group-theory.full-subgroups.md) [subgroup](group-theory.subgroups.md).

## Definitions

### The predicate of being a perfect group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-perfect-prop-Group : Prop l1
  is-perfect-prop-Group = is-full-prop-Subgroup G (commutator-subgroup-Group G)

  is-perfect-Group : UU l1
  is-perfect-Group = type-Prop is-perfect-prop-Group

  is-prop-is-perfect-Group : is-prop is-perfect-Group
  is-prop-is-perfect-Group = is-prop-type-Prop is-perfect-prop-Group
```

## External links

- [Perfect group](https://ncatlab.org/nlab/show/perfect+group) at $n$Lab
- [Perfect group](https://en.wikipedia.org/wiki/Perfect_group) at Wikipedia

A wikidata identifier was not available for this concept.
