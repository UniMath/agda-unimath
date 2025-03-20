# The category of rings

```agda
open import foundation.function-extensionality-axiom

module
  ring-theory.category-of-rings
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.large-categories funext

open import foundation.universe-levels

open import ring-theory.isomorphisms-rings funext
open import ring-theory.precategory-of-rings funext
```

</details>

## Idea

The [large category](category-theory.large-categories.md) `Ring-Category` of
[rings](ring-theory.rings.md) is the large category consisting of rings and
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
