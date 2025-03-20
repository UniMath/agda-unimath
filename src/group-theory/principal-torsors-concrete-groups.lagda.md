# Principal torsors of concrete groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.principal-torsors-concrete-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext
open import group-theory.concrete-groups funext
```

</details>

## Idea

The **principal torsor** of a [concrete group](group-theory.concrete-groups.md)
`G` is the [identity type](foundation-core.identity-types.md) of `BG`.

## Definition

```agda
module _
  {l1 : Level} (G : Concrete-Group l1)
  where

  principal-torsor-Concrete-Group :
    classifying-type-Concrete-Group G → action-Concrete-Group l1 G
  principal-torsor-Concrete-Group = Id-BG-Set G
```
