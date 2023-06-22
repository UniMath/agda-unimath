# The category of groups

```agda
module group-theory.category-of-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories

open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.isomorphisms-groups
open import group-theory.precategory-of-groups
```

</details>

## Definition

```agda
is-category-Group : is-category-Large-Precategory Group-Large-Precategory
is-category-Group G =
  fundamental-theorem-id
    ( is-contr-total-iso-Group G)
    ( iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → type-iso-Group G H → Id G H
eq-iso-Group G H = map-inv-is-equiv (is-category-Group G H)

Group-Large-Category : Large-Category lsuc (λ l1 l2 → l1 ⊔ l2)
large-precategory-Large-Category Group-Large-Category = Group-Large-Precategory
is-category-Large-Category Group-Large-Category = is-category-Group
```
