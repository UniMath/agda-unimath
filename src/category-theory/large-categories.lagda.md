# Large categories

```agda
module category-theory.large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories
open import category-theory.large-precategories

open import foundation.equivalences
open import foundation.universe-levels
```

</details>

## Idea

A large category in Homotopy Type Theory is a large precategory for which the
identities between the objects are the isomorphisms. More specifically, an
equality between objects gives rise to an isomorphism between them, by the
J-rule. A large precategory is a large category if this function is an
equivalence. Note: being a large category is a proposition since `is-equiv` is a
proposition.

## Definition

```agda
is-category-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) → UUω
is-category-Large-Precategory C =
  {l : Level} (X Y : obj-Large-Precategory C l) →
  is-equiv (iso-eq-Large-Precategory C X Y)

record Large-Cat (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor make-Large-Cat
  field
    precat-Large-Cat : Large-Precategory α β
    is-category-Large-Cat : is-category-Large-Precategory precat-Large-Cat

open Large-Cat public
```
