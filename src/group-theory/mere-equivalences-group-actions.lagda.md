# Mere equivalences of group actions

```agda
module group-theory.mere-equivalences-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.equivalences-group-actions
open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

A **mere equivalence** of [group actions](group-theory.group-actions.md) is an
element of the
[propositional truncation](foundation.propositional-truncations.md) of the type
of [equivalences of group actions](group-theory.equivalences-group-actions.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  mere-equiv-prop-action-Group : Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-prop-action-Group = trunc-Prop (equiv-action-Group G X Y)

  mere-equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-action-Group = type-Prop mere-equiv-prop-action-Group
```
