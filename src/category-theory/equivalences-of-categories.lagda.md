# Equivalences between categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.equivalences-of-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.equivalences-of-precategories funext univalence truncations
open import category-theory.functors-categories funext univalence truncations

open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-categories.md) `F : C → D` on
[categories](category-theory.categories.md) is an **equivalence** if it is an
[equivalence on the underlying precategories](category-theory.equivalences-of-precategories.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  is-equiv-functor-Category : functor-Category C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Category =
    is-equiv-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  equiv-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Category =
    equiv-Precategory (precategory-Category C) (precategory-Category D)
```
