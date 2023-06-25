# The precategory of abelian groups

```agda
module group-theory.precategory-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

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
ab-Precategory : Large-Precategory lsuc (_⊔_)
Large-Precategory.obj-Large-Precategory ab-Precategory = Ab
Large-Precategory.hom-Large-Precategory ab-Precategory = hom-Ab
Large-Precategory.comp-hom-Large-Precategory ab-Precategory
  {X = A} {B} {C} =
  comp-hom-Ab A B C
Large-Precategory.id-hom-Large-Precategory ab-Precategory
  {X = A} =
  id-hom-Ab A
Large-Precategory.associative-comp-hom-Large-Precategory ab-Precategory
  {X = A} {B} {C} {D} =
  associative-comp-hom-Ab A B C D
Large-Precategory.left-unit-law-comp-hom-Large-Precategory ab-Precategory
  {X = A} {B} =
  left-unit-law-comp-hom-Ab A B
Large-Precategory.right-unit-law-comp-hom-Large-Precategory ab-Precategory
  {X = A} {B} =
  right-unit-law-comp-hom-Ab A B
```
