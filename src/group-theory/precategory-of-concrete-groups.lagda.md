# The precategory of concrete groups

```agda
module group-theory.precategory-of-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
```

</details>

## Definitions

### The large precategory of concrete groups

```agda
Concrete-Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
obj-Large-Precategory
  Concrete-Group-Large-Precategory =
  Concrete-Group
hom-Large-Precategory
  Concrete-Group-Large-Precategory =
  hom-set-Concrete-Group
comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} {Z = K} =
  comp-hom-Concrete-Group G H K
id-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} =
  id-hom-Concrete-Group G
associative-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} {Z = K} {W = L} h g f =
  eq-htpy-hom-Concrete-Group G L _ _
    ( associative-comp-hom-Concrete-Group G H K L h g f)
left-unit-law-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} f =
  eq-htpy-hom-Concrete-Group G H _ _
    ( left-unit-law-comp-hom-Concrete-Group G H f)
right-unit-law-comp-hom-Large-Precategory
  Concrete-Group-Large-Precategory {X = G} {Y = H} f =
  eq-htpy-hom-Concrete-Group G H _ _
    ( right-unit-law-comp-hom-Concrete-Group G H f)
```
