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
  Group-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
  obj-Large-Precat Group-Large-Precat = Group
  hom-Large-Precat Group-Large-Precat = hom-Group
  compose-hom-Large-Precat Group-Large-Precat {X = G} {H} {K} =
    compose-hom-Group G H K
  id-hom-Large-Precat Group-Large-Precat {X = G} =
    id-hom-Group G
  assoc-compose-hom-Large-Precat Group-Large-Precat {X = G} {H} {K} {L} =
    assoc-compose-hom-Group G H K L
  left-unit-law-compose-hom-Large-Precat Group-Large-Precat {X = G} {H} =
    left-unit-law-compose-hom-Group G H
  right-unit-law-compose-hom-Large-Precat Group-Large-Precat {X = G} {H} =
    right-unit-law-compose-hom-Group G H
```
