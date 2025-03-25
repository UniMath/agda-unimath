# Perfect subgroups

```agda
module group-theory.perfect-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.perfect-groups
open import group-theory.subgroups
```

</details>

## Idea

A [subgroup](group-theory.subgroups.md) `H` of a [group](group-theory.groups.md)
`G` is a **perfect subgroup** if it is a
[perfect group](group-theory.perfect-groups.md) on its own.

## Definitions

### The predicate of being a perfect subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-perfect-prop-Subgroup : Prop (l1 ⊔ l2)
  is-perfect-prop-Subgroup = is-perfect-prop-Group (group-Subgroup G H)

  is-perfect-Subgroup : UU (l1 ⊔ l2)
  is-perfect-Subgroup = type-Prop is-perfect-prop-Subgroup

  is-prop-is-perfect-Subgroup : is-prop is-perfect-Subgroup
  is-prop-is-perfect-Subgroup = is-prop-type-Prop is-perfect-prop-Subgroup
```

## External links

A wikidata identifier was not available for this concept.
