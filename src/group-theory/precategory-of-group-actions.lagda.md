# The precategory of group actions

```agda
module group-theory.precategory-of-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
```

</details>

## Definitions

### The large precategory of G-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Abstract-Group-Action-Large-Precategory :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  obj-Large-Precategory
    Abstract-Group-Action-Large-Precategory =
    Abstract-Group-Action G
  hom-set-Large-Precategory
    Abstract-Group-Action-Large-Precategory =
    hom-set-Abstract-Group-Action G
  comp-hom-Large-Precategory
    Abstract-Group-Action-Large-Precategory {X = X} {Y} {Z} =
    comp-hom-Abstract-Group-Action G X Y Z
  id-hom-Large-Precategory
    Abstract-Group-Action-Large-Precategory {X = X} =
    id-hom-Abstract-Group-Action G X
  associative-comp-hom-Large-Precategory
    Abstract-Group-Action-Large-Precategory {X = X} {Y} {Z} {W} =
    associative-comp-hom-Abstract-Group-Action G X Y Z W
  left-unit-law-comp-hom-Large-Precategory
    Abstract-Group-Action-Large-Precategory {X = X} {Y} =
    left-unit-law-comp-hom-Abstract-Group-Action G X Y
  right-unit-law-comp-hom-Large-Precategory
    Abstract-Group-Action-Large-Precategory {X = X} {Y} =
    right-unit-law-comp-hom-Abstract-Group-Action G X Y
```

### The small precategory of G-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Abstract-Group-Action-Precategory :
    (l2 : Level) → Precategory (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 (Abstract-Group-Action-Precategory l2) = Abstract-Group-Action G l2
  pr1 (pr2 (Abstract-Group-Action-Precategory l2)) =
    hom-set-Abstract-Group-Action G
  pr1 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precategory l2)))) {X} {Y} {Z} =
    comp-hom-Abstract-Group-Action G X Y Z
  pr2 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precategory l2)))) {X} {Y} {Z} {W} =
    associative-comp-hom-Abstract-Group-Action G X Y Z W
  pr1 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precategory l2)))) =
    id-hom-Abstract-Group-Action G
  pr1 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precategory l2))))) {X} {Y} =
    left-unit-law-comp-hom-Abstract-Group-Action G X Y
  pr2 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precategory l2))))) {X} {Y} =
    right-unit-law-comp-hom-Abstract-Group-Action G X Y
```
