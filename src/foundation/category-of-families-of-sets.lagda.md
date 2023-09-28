# The category of families of sets

```agda
module foundation.category-of-families-of-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories
open import category-theory.large-function-categories
open import category-theory.large-function-precategories
open import category-theory.large-precategories

open import foundation.category-of-sets
open import foundation.universe-levels
```

</details>

## Idea

The **[large category](category-theory.large-categories.md) of families of
[sets](foundation.sets.md) over a type** `A` is the
[large function category](category-theory.large-function-categories.md)
`A → Set`.

## Definition

### The large precategory of families of sets over a type

```agda
Family-Of-Sets-Large-Precategory :
  {l : Level} → UU l →
  Large-Precategory (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
Family-Of-Sets-Large-Precategory A =
  Large-Function-Precategory A Set-Large-Precategory
```

### The large category of families of sets over a type

```agda
module _
  {l : Level} (A : UU l)
  where

  Family-Of-Sets-Large-Category :
    Large-Category (λ l1 → l ⊔ lsuc l1) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  Family-Of-Sets-Large-Category =
    Large-Function-Category A Set-Large-Category

  is-large-category-Family-Of-Sets-Large-Category :
    is-large-category-Large-Precategory (Family-Of-Sets-Large-Precategory A)
  is-large-category-Family-Of-Sets-Large-Category =
    is-large-category-Large-Category Family-Of-Sets-Large-Category
```
