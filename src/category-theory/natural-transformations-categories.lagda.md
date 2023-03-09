# Natural transformations between functors between categories

```agda
module category-theory.natural-transformations-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-transformations-precategories

open import foundation.universe-levels
```

</details>

## Idea

A natural transformation between functors on categories is a natural transformation between the functors on the underlying precategories.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Cat l1 l2)
  (D : Cat l3 l4)
  (F G : functor-Cat C D) where

  is-nat-trans-Cat : ((x : obj-Cat C) → type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x))
                   → UU (l1 ⊔ l2 ⊔ l4)
  is-nat-trans-Cat = is-nat-trans-Precat (precat-Cat C) (precat-Cat D) F G

  nat-trans-Cat : UU (l1 ⊔ l2 ⊔ l4)
  nat-trans-Cat = nat-trans-Precat (precat-Cat C) (precat-Cat D) F G

  components-nat-trans-Cat : nat-trans-Cat → (x : obj-Cat C) → type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x)
  components-nat-trans-Cat = components-nat-trans-Precat (precat-Cat C) (precat-Cat D) F G
```
