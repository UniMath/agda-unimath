# The category of semigroups

```agda
module group-theory.category-of-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.isomorphisms-semigroups
open import group-theory.precategory-of-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Since isomorphic semigroups are equal, the precategory of semigroups is a category.

## Definition

```agda
is-category-Semigroup :
  is-category-Large-Precat Semigroup-Large-Precat
is-category-Semigroup G =
  fundamental-theorem-id
    ( is-contr-total-iso-Semigroup G)
    ( iso-eq-Semigroup G)

extensionality-Semigroup :
  {l : Level} (G H : Semigroup l) → Id G H ≃ type-iso-Semigroup G H
pr1 (extensionality-Semigroup G H) = iso-eq-Semigroup G H
pr2 (extensionality-Semigroup G H) = is-category-Semigroup G H

eq-iso-Semigroup :
  {l : Level} (G H : Semigroup l) → type-iso-Semigroup G H → Id G H
eq-iso-Semigroup G H = map-inv-is-equiv (is-category-Semigroup G H)

Semigroup-Large-Cat : Large-Cat lsuc (λ l1 l2 → l1 ⊔ l2)
precat-Large-Cat Semigroup-Large-Cat = Semigroup-Large-Precat
is-category-Large-Cat Semigroup-Large-Cat = is-category-Semigroup
```
