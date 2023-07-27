# The precategory of groups

```agda
module group-theory.precategory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
```

</details>

## Definition

```agda
instance
  Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
  obj-Large-Precategory Group-Large-Precategory = Group
  hom-Large-Precategory Group-Large-Precategory = hom-Group
  comp-hom-Large-Precategory Group-Large-Precategory {X = G} {H} {K} =
    comp-hom-Group G H K
  id-hom-Large-Precategory Group-Large-Precategory {X = G} =
    id-hom-Group G
  associative-comp-hom-Large-Precategory
    Group-Large-Precategory {X = G} {H} {K} {L} =
    associative-comp-hom-Group G H K L
  left-unit-law-comp-hom-Large-Precategory
    Group-Large-Precategory {X = G} {H} =
    left-unit-law-comp-hom-Group G H
  right-unit-law-comp-hom-Large-Precategory
    Group-Large-Precategory {X = G} {H} =
    right-unit-law-comp-hom-Group G H
```
