# Natural isomorphisms between functors between categories

```agda
module category-theory.natural-isomorphisms-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.natural-transformations-categories

open import foundation.universe-levels
```

</details>

## Idea

A natural isomorphism between functors on categories is a natural isomorphism
between the functors on the underlying precategories.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Cat l1 l2)
  (D : Cat l3 l4)
  (F G : functor-Cat C D)
  where

  is-natural-isomorphism-Cat : natural-transformation-Cat C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-Cat =
    is-natural-isomorphism-Precat (precat-Cat C) (precat-Cat D) F G

  natural-isomorphism-Cat : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-Cat =
    natural-isomorphism-Precat (precat-Cat C) (precat-Cat D) F G
```
