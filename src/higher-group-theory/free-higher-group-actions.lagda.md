# Free higher group actions

```agda
module higher-group-theory.free-higher-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions
open import higher-group-theory.higher-groups
open import higher-group-theory.orbits-higher-group-actions
```

</details>

## Idea

A higher group action is said to be free if its type of orbits is a set.

## Definition

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-free-action-∞-Group-Prop : Prop (l1 ⊔ l2)
  is-free-action-∞-Group-Prop = is-set-Prop (orbit-action-∞-Group G X)

  is-free-action-∞-Group : UU (l1 ⊔ l2)
  is-free-action-∞-Group = type-Prop is-free-action-∞-Group-Prop

  is-prop-is-free-action-∞-Group : is-prop is-free-action-∞-Group
  is-prop-is-free-action-∞-Group = is-prop-type-Prop is-free-action-∞-Group-Prop

free-action-∞-Group :
  {l1 : Level} (l2 : Level) → ∞-Group l1 → UU (l1 ⊔ lsuc l2)
free-action-∞-Group l2 G =
  type-subtype (is-free-action-∞-Group-Prop {l2 = l2} G)
```
