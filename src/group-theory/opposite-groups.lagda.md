# The opposite of a group

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.opposite-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.groups funext
open import group-theory.isomorphisms-groups funext
open import group-theory.monoids funext
open import group-theory.opposite-semigroups funext
```

</details>

## Idea

The **opposite of a [group](group-theory.groups.md)** `G` with multiplication
`μ` is a group with the same underlying [set](foundation-core.sets.md) as `G`
and multiplication given by `x y ↦ μ y x`.

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  is-unital-op-Group : is-unital-Semigroup (op-Semigroup (semigroup-Group G))
  pr1 is-unital-op-Group = unit-Group G
  pr1 (pr2 is-unital-op-Group) = right-unit-law-mul-Group G
  pr2 (pr2 is-unital-op-Group) = left-unit-law-mul-Group G

  is-group-op-Group : is-group-Semigroup (op-Semigroup (semigroup-Group G))
  pr1 is-group-op-Group = is-unital-op-Group
  pr1 (pr2 is-group-op-Group) = inv-Group G
  pr1 (pr2 (pr2 is-group-op-Group)) = right-inverse-law-mul-Group G
  pr2 (pr2 (pr2 is-group-op-Group)) = left-inverse-law-mul-Group G

  op-Group : Group l
  pr1 op-Group = op-Semigroup (semigroup-Group G)
  pr2 op-Group = is-group-op-Group
```

## Properties

### The opposite group of `G` is isomorphic to `G`

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-inv-Group : equiv-Group G (op-Group G)
  pr1 equiv-inv-Group = equiv-equiv-inv-Group G
  pr2 equiv-inv-Group = distributive-inv-mul-Group G

  iso-inv-Group : iso-Group G (op-Group G)
  iso-inv-Group = iso-equiv-Group G (op-Group G) equiv-inv-Group
```
