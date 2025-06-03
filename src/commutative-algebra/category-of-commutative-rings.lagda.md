# The category of commutative rings

```agda
module commutative-algebra.category-of-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories

open import commutative-algebra.isomorphisms-commutative-rings
open import commutative-algebra.precategory-of-commutative-rings

open import foundation.universe-levels
```

</details>

## Idea

The [large category](category-theory.large-categories.md)
`Commutative-Ring-Category` of
[commutative rings](commutative-algebra.commutative-rings.md) is the large
category consisting of commutative rings and
[ring homomorphisms](commutative-algebra.homomorphisms-commutative-rings.md).

## Definitions

### The large category of commutative rings

```agda
is-large-category-Commutative-Ring-Large-Category :
  is-large-category-Large-Precategory Commutative-Ring-Large-Precategory
is-large-category-Commutative-Ring-Large-Category =
  is-equiv-iso-eq-Commutative-Ring

Commutative-Ring-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Commutative-Ring-Large-Category =
  Commutative-Ring-Large-Precategory
is-large-category-Large-Category Commutative-Ring-Large-Category =
  is-large-category-Commutative-Ring-Large-Category
```

### The small categories of commutative rings

```agda
Commutative-Ring-Category : (l : Level) → Category (lsuc l) l
Commutative-Ring-Category =
  category-Large-Category Commutative-Ring-Large-Category
```
