# The category of rings

```agda
module ring-theory.category-of-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories

open import foundation.universe-levels

open import ring-theory.isomorphisms-rings
open import ring-theory.precategory-of-rings
```

</details>

## Idea

The [large category](category-theory.large-categories.md) `Ring-Large-Category`
of [rings](ring-theory.rings.md) is the large category consisting of rings and
[ring homomorphisms](ring-theory.homomorphisms-rings.md).

## Definitions

### The large category of rings

```agda
is-large-category-Ring-Large-Category :
  is-large-category-Large-Precategory Ring-Large-Precategory
is-large-category-Ring-Large-Category =
  is-equiv-iso-eq-Ring

Ring-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Ring-Large-Category =
  Ring-Large-Precategory
is-large-category-Large-Category Ring-Large-Category =
  is-large-category-Ring-Large-Category
```

### The small categories of rings

```agda
Ring-Category : (l : Level) → Category (lsuc l) l
Ring-Category = category-Large-Category Ring-Large-Category
```
