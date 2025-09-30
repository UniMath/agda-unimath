# The category of groups

```agda
module group-theory.category-of-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories

open import foundation.1-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.isomorphisms-groups
open import group-theory.precategory-of-groups
```

</details>

## Definitions

```agda
is-large-category-Group :
  is-large-category-Large-Precategory Group-Large-Precategory
is-large-category-Group G =
  fundamental-theorem-id (is-torsorial-iso-Group G) (iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → iso-Group G H → G ＝ H
eq-iso-Group G H = map-inv-is-equiv (is-large-category-Group G H)

Group-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Group-Large-Category = Group-Large-Precategory
is-large-category-Large-Category Group-Large-Category = is-large-category-Group

Group-Category : (l : Level) → Category (lsuc l) l
Group-Category = category-Large-Category Group-Large-Category
```

## Corollaries

### The type of groups is a 1-type

```agda
is-1-type-Group : {l : Level} → is-1-type (Group l)
is-1-type-Group {l} = is-1-type-obj-Category (Group-Category l)
```
