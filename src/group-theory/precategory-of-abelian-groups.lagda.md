# The precategory of abelian groups

```agda
module group-theory.precategory-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
```

</details>

## Idea

The **precategory of abelian groups** consists of abelian groups and group
homomorphisms.

## Definition

### The large precategory of abelian groups

```agda
Ab-Large-Precategory : Large-Precategory lsuc (_⊔_)
Large-Precategory.obj-Large-Precategory
  Ab-Large-Precategory =
  Ab
Large-Precategory.hom-set-Large-Precategory
  Ab-Large-Precategory =
  hom-set-Ab
Large-Precategory.comp-hom-Large-Precategory
  Ab-Large-Precategory {X = A} {B} {C} =
  comp-hom-Ab A B C
Large-Precategory.id-hom-Large-Precategory
  Ab-Large-Precategory {X = A} =
  id-hom-Ab A
Large-Precategory.associative-comp-hom-Large-Precategory
  Ab-Large-Precategory {X = A} {B} {C} {D} =
  associative-comp-hom-Ab A B C D
Large-Precategory.left-unit-law-comp-hom-Large-Precategory
  Ab-Large-Precategory {X = A} {B} =
  left-unit-law-comp-hom-Ab A B
Large-Precategory.right-unit-law-comp-hom-Large-Precategory
  Ab-Large-Precategory {X = A} {B} =
  right-unit-law-comp-hom-Ab A B
```

### The small categories of abelian groups

```agda
Ab-Precategory : (l : Level) → Precategory (lsuc l) l
Ab-Precategory = precategory-Large-Precategory Ab-Large-Precategory
```
