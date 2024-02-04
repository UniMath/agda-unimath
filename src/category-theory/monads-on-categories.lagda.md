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
  {l : Level} (C : Category l l)
  where

  monad-Category : UU l
  monad-Category = monad-Precategory l (precategory-Category C)
```
