# Principal torsors of concrete groups

```agda
module group-theory.principal-torsors-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
```

</details>

## Idea

The principal torsor of a concrete group `G` is the identity type of `BG`.

## Definition

```agda
module _
  {l1 : Level} (G : Concrete-Group l1)
  where

  principal-torsor-Concrete-Group :
    classifying-type-Concrete-Group G → action-Concrete-Group l1 G
  principal-torsor-Concrete-Group = Id-BG-Set G
```
