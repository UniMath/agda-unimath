# Free concrete group actions

```agda
module group-theory.free-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.orbits-concrete-group-actions
```

</details>

## Definition

```agda
is-free-action-Concrete-Group-Prop :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  Prop (l1 ⊔ l2)
is-free-action-Concrete-Group-Prop G X =
  is-set-Prop (orbit-action-Concrete-Group G X)

is-free-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  UU (l1 ⊔ l2)
is-free-action-Concrete-Group G X =
  type-Prop (is-free-action-Concrete-Group-Prop G X)

is-prop-is-free-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  is-prop (is-free-action-Concrete-Group G X)
is-prop-is-free-action-Concrete-Group G X =
  is-prop-type-Prop (is-free-action-Concrete-Group-Prop G X)
```
