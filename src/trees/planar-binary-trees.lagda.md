# Planar binary trees

```agda
module trees.planar-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.empty-types
open import foundation.function-types
open import foundation.universe-levels

open import trees.w-types
```

</details>

## Idea

A
{{#concept "planar binary tree" WD="binary tree" WDID=Q380172 Agda=Planar-Bin-Tree}}
is a binary tree in which the branchings are labeled by the
[booleans](foundation.booleans.md). The idea is that at any branching point in a
planar binary tree, we know which branch goes to the left and which branch goes
to the right.

Planar binary trees are commonly called binary trees, but in univalent
mathematics it makes sense to recognize that the branching points in a binary
tree should not record which branch goes left and which branch goes right.

## Definitions

### The inductive definition of the type of planar binary trees

```agda
data Planar-Bin-Tree : UU lzero where
  root-PBT : Planar-Bin-Tree
  join-PBT : (x y : Planar-Bin-Tree) → Planar-Bin-Tree
```

### The definition of the type of planar binary trees as a W-type

```agda
PBT-𝕎 : UU lzero
PBT-𝕎 = 𝕎 bool P
  where
  P : bool → UU lzero
  P true = bool
  P false = empty

root-PBT-𝕎 : PBT-𝕎
root-PBT-𝕎 = constant-𝕎 false id

join-PBT-𝕎 : (x y : PBT-𝕎) → PBT-𝕎
join-PBT-𝕎 x y = tree-𝕎 true α
  where
  α : bool → PBT-𝕎
  α true = x
  α false = y
```
