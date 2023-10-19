# Characteristic subgroups

```agda
module group-theory.characteristic-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.isomorphisms-groups
open import group-theory.subgroups
```

</details>

## Idea

A **characteristic subgroup** of a [group](group-theory.groups.md) `G` is a
[subgroup](group-theory.subgroups.md) `H` of `G` such that `e H ⊆ H` for every
[isomorphism](group-theory.isomorphisms-groups.md) `e : G ≅ G`. The seemingly
stronger condition, which asserts that `e H ＝ H` for every isomorphism
`e : G ≅ G` is equivalent.

Note that any characteristic subgroup is
[normal](group-theory.normal-subgroups.md), since the condition of being
characteristic implies that `conjugation x H ＝ H`.

## Definition

### The predicate of being a characteristic subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-characteristic-prop-Subgroup : Prop (l1 ⊔ l2)
  is-characteristic-prop-Subgroup =
    Π-Prop
      ( iso-Group G G)
      ( λ e →
        leq-prop-Subgroup G
          ( im-hom-Subgroup G G (hom-iso-Group G G e) H)
          ( H))
```

### The stronger predicate of being a characteristic subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-characteristic-prop-Subgroup' : Prop (l1 ⊔ l2)
  is-characteristic-prop-Subgroup' =
    Π-Prop
      ( iso-Group G G)
      ( λ e →
        has-same-elements-prop-Subgroup G
          ( im-hom-Subgroup G G (hom-iso-Group G G e) H)
          ( H))
```

## See also

- [Characteristic subgroup](https://groupprops.subwiki.org/wiki/Characteristic_subgroup)
  at Groupprops
- [Characteristic subgroup](https://www.wikidata.org/entity/Q747027) at Wikidata
- [Characteristic subgroup](https://en.wikipedia.org/wiki/Characteristic_subgroup)
  at Wikipedia
