# The precategory of functors and natural transformations between two fixed precategories

```agda
module category-theory.precategory-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

### Precategory of functors

Functors between precategories and natural transformations between them introduce a
new precategory whose identity map and composition structure are inherited pointwise
from the codomain precategory.

```agda

module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where

  functor-Precat-Precat : Precat (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-Precat-Precat = functor-Precat C D
  pr1 (pr2 functor-Precat-Precat) F G = nat-trans-Precat-Set C D F G
  pr1 (pr2 (pr2 functor-Precat-Precat)) =
    (λ {F} {G} {H} α β → comp-nat-trans-Precat C D F G H α β) ,
    λ {F} {G} {H} {I} h g f → assoc-comp-nat-trans-Precat C D {F} {G} {H} {I} f g h
  pr2 (pr2 (pr2 functor-Precat-Precat)) =
    (λ F → id-nat-trans-Precat C D F) ,
    (λ {F} {G} α → left-unit-law-comp-nat-trans-Precat C D {F} {G} α) ,
    (λ {F} {G} α → right-unit-law-comp-nat-trans-Precat C D {F} {G} α)
```
