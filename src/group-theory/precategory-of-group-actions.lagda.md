# The precategory of group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.precategory-of-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories funext
open import category-theory.precategories funext

open import foundation.universe-levels

open import group-theory.group-actions funext
open import group-theory.groups funext
open import group-theory.homomorphisms-group-actions funext
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
  action-Group-Large-Precategory =
    make-Large-Precategory
      ( action-Group G)
      ( hom-set-action-Group G)
      ( λ {l1} {l2} {l3} {X} {Y} {Z} → comp-hom-action-Group G X Y Z)
      ( λ {l1} {X} → id-hom-action-Group G X)
      ( λ {l1} {l2} {l3} {l4} {X} {Y} {Z} {W} →
        associative-comp-hom-action-Group G X Y Z W)
      ( λ {l1} {l2} {X} {Y} → left-unit-law-comp-hom-action-Group G X Y)
      ( λ {l1} {l2} {X} {Y} → right-unit-law-comp-hom-action-Group G X Y)
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
