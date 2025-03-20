# Characteristic subgroups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.characteristic-subgroups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions funext
open import foundation.universe-levels

open import group-theory.groups funext
open import group-theory.images-of-group-homomorphisms funext
open import group-theory.isomorphisms-groups funext
open import group-theory.subgroups funext
```

</details>

## Idea

A **characteristic subgroup** of a [group](group-theory.groups.md) `G` is a
[subgroup](group-theory.subgroups.md) `H` of `G` such that `f H ⊆ H` for every
[isomorphism](group-theory.isomorphisms-groups.md) `f : G ≅ G`. The seemingly
stronger condition, which asserts that `f H ＝ H` for every isomorphism
`f : G ≅ G` is equivalent.

Note that any characteristic subgroup is
[normal](group-theory.normal-subgroups.md), since the condition of being
characteristic implies that `conjugation x H ＝ H`.

We also note that every subgroup which is defined for all groups, such as the
commutator subgroup, is automatically characteristic as a consequence of the
[univalence axiom](foundation.univalence.md), and therefore also normal.

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
      ( λ f →
        leq-prop-Subgroup G
          ( im-hom-Subgroup G G (hom-iso-Group G G f) H)
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
      ( λ f →
        has-same-elements-prop-Subgroup G
          ( im-hom-Subgroup G G (hom-iso-Group G G f) H)
          ( H))
```

## See also

- [Characteristic subgroup](https://groupprops.subwiki.org/wiki/Characteristic_subgroup)
  at Groupprops
- [Characteristic subgroup](https://www.wikidata.org/entity/Q747027) at Wikidata
- [Characteristic subgroup](https://en.wikipedia.org/wiki/Characteristic_subgroup)
  at Wikipedia
