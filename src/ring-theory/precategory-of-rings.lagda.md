# The precategory of rings

```agda
module ring-theory.precategory-of-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

The **(large) precategory of rings** consists of [rings](ring-theory.rings.md)
and [ring homomorphisms](ring-theory.homomorphisms-rings.md).

## Definitions

### The large precategory of rings

```agda
Ring-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Ring-Large-Precategory =
  Ring
hom-set-Large-Precategory
  Ring-Large-Precategory =
  hom-set-Ring
comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} {T} =
  comp-hom-Ring R S T
id-hom-Large-Precategory
  Ring-Large-Precategory {X = R} =
  id-hom-Ring R
associative-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} {T} {U} =
  associative-comp-hom-Ring R S T U
left-unit-law-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} =
  left-unit-law-comp-hom-Ring R S
right-unit-law-comp-hom-Large-Precategory
  Ring-Large-Precategory {X = R} {S} =
  right-unit-law-comp-hom-Ring R S
```

### The precategory or rings of universe level `l`

```agda
Ring-Precategory : (l : Level) → Precategory (lsuc l) l
Ring-Precategory = precategory-Large-Precategory Ring-Large-Precategory
```
