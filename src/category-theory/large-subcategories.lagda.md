# Large subcategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.large-subcategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories funext univalence truncations
open import category-theory.large-subprecategories funext univalence truncations

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
