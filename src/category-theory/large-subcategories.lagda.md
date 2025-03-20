# Large subcategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.large-subcategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories funext
open import category-theory.large-subprecategories funext

open import foundation.universe-levels
```

</details>

## Idea

A **large subcategory** of a
[large category](category-theory.large-categories.md) `C` is a
[large subprecategory](category-theory.large-subprecategories.md) `P` of the
underlying [large precategory](category-theory.large-precategories.md) of `C`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level → Level) (δ : Level → Level → Level)
  (C : Large-Category α β)
  where

  Large-Subcategory : UUω
  Large-Subcategory =
    Large-Subprecategory γ δ (large-precategory-Large-Category C)
```
