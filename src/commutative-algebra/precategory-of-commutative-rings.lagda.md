# The precategory of commutative rings

```agda
module commutative-algebra.precategory-of-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings

open import foundation.universe-levels
```

</details>

## Idea

The **precategory of commutative rings** consists of commutative rings and
homomorphisms of commutative rings.

## Definitions

### The large precategory of commutative rings

```agda
Commutative-Ring-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Commutative-Ring-Large-Precategory =
  Commutative-Ring
hom-set-Large-Precategory
  Commutative-Ring-Large-Precategory =
  hom-set-Commutative-Ring
comp-hom-Large-Precategory
  Commutative-Ring-Large-Precategory {X = A} {B} {C} =
  comp-hom-Commutative-Ring A B C
id-hom-Large-Precategory
  Commutative-Ring-Large-Precategory {X = A} =
  id-hom-Commutative-Ring A
associative-comp-hom-Large-Precategory
  Commutative-Ring-Large-Precategory {X = A} {B} {C} {D} =
  associative-comp-hom-Commutative-Ring A B C D
left-unit-law-comp-hom-Large-Precategory
  Commutative-Ring-Large-Precategory {X = A} {B} =
  left-unit-law-comp-hom-Commutative-Ring A B
right-unit-law-comp-hom-Large-Precategory
  Commutative-Ring-Large-Precategory {X = A} {B} =
  right-unit-law-comp-hom-Commutative-Ring A B
```

### The precategory of commutative rings of universe level `l`

```agda
Commutative-Ring-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Ring-Precategory =
  precategory-Large-Precategory Commutative-Ring-Large-Precategory
```
