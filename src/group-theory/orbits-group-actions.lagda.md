# Orbits of group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.orbits-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.group-actions funext
open import group-theory.groups funext
```

</details>

## Idea

The [groupoid](category-theory.groupoids.md) of **orbits** of a
[group action](group-theory.group-actions.md) consists of elements of `X`, and a
morphism from `x` to `y` is given by an element `g` of the
[group](group-theory.groups.md) `G` such that `gx ＝ y`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  hom-orbit-action-Group :
    (x y : type-action-Group G X) → UU (l1 ⊔ l2)
  hom-orbit-action-Group x y =
    Σ (type-Group G) (λ g → mul-action-Group G X g x ＝ y)
```
