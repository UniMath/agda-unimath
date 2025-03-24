# Perfect groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.perfect-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.commutator-subgroups funext univalence truncations
open import group-theory.full-subgroups funext univalence truncations
open import group-theory.groups funext univalence truncations
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
