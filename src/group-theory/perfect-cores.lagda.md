# Perfect cores

```agda
module group-theory.perfect-cores where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.perfect-subgroups
open import group-theory.subgroups
```

</details>

## Idea

The **perfect core** of a [group](group-theory.groups.md) `G` is the largest
[perfect subgroup](group-theory.perfect-subgroups.md) of `G`. That is, the
[subgroup](group-theory.subgroups.md) `perfect-core G` satisfies the following
universal property:

```text
  (H : Subgroup G) → is-perfect-Subgroup G H ↔ H ⊆ perfect-core G
```

## Definitions

### The predicate of being a perfect core

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-perfect-core-Subgroup : UUω
  is-perfect-core-Subgroup =
    {l : Level} (K : Subgroup l G) →
    is-perfect-Subgroup G K ↔ leq-Subgroup G K H
```

## External links

- [Perfect core](https://en.wikipedia.org/wiki/Perfect_core) at Wikipedia

A wikidata identifier was not available for this concept.
