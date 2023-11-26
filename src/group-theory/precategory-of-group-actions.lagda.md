# The precategory of group actions

```agda
module group-theory.precategory-of-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
```

</details>

## Idea

The [large precategory](category-theory.large-precategories.md) of
[group actions](group-theory.group-actions.md) consists of group actions and
[morphisms of group actions](group-theory.homomorphisms-group-actions.md)
between them.

## Definitions

### The large precategory of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group-Large-Precategory :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  obj-Large-Precategory
    action-Group-Large-Precategory =
    action-Group G
  hom-set-Large-Precategory
    action-Group-Large-Precategory =
    hom-set-action-Group G
  comp-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} {Y} {Z} =
    comp-hom-action-Group G X Y Z
  id-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} =
    id-hom-action-Group G X
  associative-comp-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} {Y} {Z} {W} =
    associative-comp-hom-action-Group G X Y Z W
  inv-associative-comp-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} {Y} {Z} {W} =
    inv-associative-comp-hom-action-Group G X Y Z W
  left-unit-law-comp-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} {Y} =
    left-unit-law-comp-hom-action-Group G X Y
  right-unit-law-comp-hom-Large-Precategory
    action-Group-Large-Precategory {X = X} {Y} =
    right-unit-law-comp-hom-action-Group G X Y
```

### The small precategory of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group-Precategory :
    (l2 : Level) → Precategory (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  action-Group-Precategory =
    precategory-Large-Precategory (action-Group-Large-Precategory G)
```
