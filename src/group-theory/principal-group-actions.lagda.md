# Principal group actions

```agda
module group-theory.principal-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

The **principal group action** is the [action](group-theory.group-actions.md) of
a [group](group-theory.groups.md) on itself by multiplication from the left.

## Definition

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  principal-action-Group : action-Group G l1
  pr1 principal-action-Group = set-Group G
  pr1 (pr2 principal-action-Group) g = equiv-mul-Group G g
  pr2 (pr2 principal-action-Group) {g} {h} =
    eq-htpy-equiv (associative-mul-Group G g h)
```
