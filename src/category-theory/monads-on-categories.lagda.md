# Monads on categories

```agda
module category-theory.monads-on-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.monads-on-precategories
open import category-theory.precategories

open import foundation.universe-levels
```

</details>

## Definitions

### The type of monads on categories

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  monad-Category : UU (l1 ⊔ l2)
  monad-Category = monad-Precategory (precategory-Category C)
```
