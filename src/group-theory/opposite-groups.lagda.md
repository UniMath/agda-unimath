# The opposite of a group

```agda
module group-theory.opposite-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.isomorphisms-groups
```

</details>

## Idea

The opposite of a group `G` with multiplication `μ` is a group with the same underlying set as `G` and multiplication given by `x y ↦ μ y x`.

## Definition

```agda
op-Group : {l : Level} → Group l → Group l
pr1 (pr1 (op-Group G)) = set-Group G
pr1 (pr2 (pr1 (op-Group G))) x y = mul-Group G y x
pr2 (pr2 (pr1 (op-Group G))) x y z = inv (associative-mul-Group G z y x)
pr1 (pr1 (pr2 (op-Group G))) = unit-Group G
pr1 (pr2 (pr1 (pr2 (op-Group G)))) = right-unit-law-mul-Group G
pr2 (pr2 (pr1 (pr2 (op-Group G)))) = left-unit-law-mul-Group G
pr1 (pr2 (pr2 (op-Group G))) = inv-Group G
pr1 (pr2 (pr2 (pr2 (op-Group G)))) = right-inverse-law-mul-Group G
pr2 (pr2 (pr2 (pr2 (op-Group G)))) = left-inverse-law-mul-Group G
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

  iso-inv-Group : type-iso-Group G (op-Group G)
  iso-inv-Group = iso-equiv-Group G (op-Group G) equiv-inv-Group
```
