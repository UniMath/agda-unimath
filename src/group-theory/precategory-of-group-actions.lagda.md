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

  Abstract-Group-Action-Large-Precat :
    Large-Precat (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  obj-Large-Precat Abstract-Group-Action-Large-Precat =
    Abstract-Group-Action G
  hom-Large-Precat Abstract-Group-Action-Large-Precat =
    hom-Abstract-Group-Action G
  comp-hom-Large-Precat Abstract-Group-Action-Large-Precat {X = X} {Y} {Z} =
    comp-hom-Abstract-Group-Action G X Y Z
  id-hom-Large-Precat Abstract-Group-Action-Large-Precat {X = X} =
    id-hom-Abstract-Group-Action G X
  associative-comp-hom-Large-Precat Abstract-Group-Action-Large-Precat
    {X = X} {Y} {Z} {W} =
    associative-comp-hom-Abstract-Group-Action G X Y Z W
  left-unit-law-comp-hom-Large-Precat Abstract-Group-Action-Large-Precat
    {X = X} {Y} =
    left-unit-law-comp-hom-Abstract-Group-Action G X Y
  right-unit-law-comp-hom-Large-Precat Abstract-Group-Action-Large-Precat
    {X = X} {Y} =
    right-unit-law-comp-hom-Abstract-Group-Action G X Y
```

### The small precategory of G-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Abstract-Group-Action-Precat : (l2 : Level) → Precat (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 (Abstract-Group-Action-Precat l2) = Abstract-Group-Action G l2
  pr1 (pr2 (Abstract-Group-Action-Precat l2)) = hom-Abstract-Group-Action G
  pr1 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) {X} {Y} {Z} =
    comp-hom-Abstract-Group-Action G X Y Z
  pr2 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) {X} {Y} {Z} {W} =
    associative-comp-hom-Abstract-Group-Action G X Y Z W
  pr1 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) =
    id-hom-Abstract-Group-Action G
  pr1 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2))))) {X} {Y} =
    left-unit-law-comp-hom-Abstract-Group-Action G X Y
  pr2 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2))))) {X} {Y} =
    right-unit-law-comp-hom-Abstract-Group-Action G X Y
```
