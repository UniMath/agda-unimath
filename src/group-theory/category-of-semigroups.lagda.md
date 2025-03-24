# The category of semigroups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.category-of-semigroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.large-categories funext univalence truncations

open import foundation.1-types funext univalence
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.isomorphisms-semigroups funext univalence truncations
open import group-theory.precategory-of-semigroups funext univalence truncations
open import group-theory.semigroups funext univalence
```

</details>

## Idea

Since isomorphic semigroups are equal, the precategory of semigroups is a
category.

## Definition

### The large category of semigroups

```agda
is-large-category-Semigroup :
  is-large-category-Large-Precategory Semigroup-Large-Precategory
is-large-category-Semigroup G =
  fundamental-theorem-id (is-torsorial-iso-Semigroup G) (iso-eq-Semigroup G)

extensionality-Semigroup :
  {l : Level} (G H : Semigroup l) → Id G H ≃ iso-Semigroup G H
pr1 (extensionality-Semigroup G H) = iso-eq-Semigroup G H
pr2 (extensionality-Semigroup G H) = is-large-category-Semigroup G H

eq-iso-Semigroup :
  {l : Level} (G H : Semigroup l) → iso-Semigroup G H → Id G H
eq-iso-Semigroup G H = map-inv-is-equiv (is-large-category-Semigroup G H)

Semigroup-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Semigroup-Large-Category =
  Semigroup-Large-Precategory
is-large-category-Large-Category Semigroup-Large-Category =
  is-large-category-Semigroup
```

### The category of small semigroups

```agda
Semigroup-Category : (l : Level) → Category (lsuc l) l
Semigroup-Category = category-Large-Category Semigroup-Large-Category
```

## Corollaries

### The type of semigroups is a 1-type

```agda
is-1-type-Semigroup : {l : Level} → is-1-type (Semigroup l)
is-1-type-Semigroup {l} = is-1-type-obj-Category (Semigroup-Category l)
```
