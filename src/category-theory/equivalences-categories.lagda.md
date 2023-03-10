# Equivalences between categories

```agda
module category-theory.equivalences-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.equivalences-precategories
open import category-theory.functors-categories

open import foundation.universe-levels
```

</details>

## Idea

A functor `F : C → D` on categories is an equivalence if it is an equivalence on the underlying precategories.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Cat l1 l2)
  (D : Cat l3 l4) where

  is-equiv-functor-Cat : functor-Cat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Cat = is-equiv-functor-Precat (precat-Cat C) (precat-Cat D)

  equiv-Cat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Cat = equiv-Precat (precat-Cat C) (precat-Cat D)
```
