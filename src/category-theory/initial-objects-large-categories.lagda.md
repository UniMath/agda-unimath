# Initial objects of large categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.initial-objects-large-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.initial-objects-large-precategories funext univalence truncations
open import category-theory.large-categories funext univalence truncations

open import foundation.universe-levels
```

</details>

## Idea

An **initial object** in a [large category](category-theory.large-categories.md)
`C` is an object `X` such that `hom X Y` is
[contractible](foundation.contractible-types.md) for any object `Y`.

## Definitions

### Initial objects in large categories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  {l : Level} (X : obj-Large-Category C l)
  where

  is-initial-obj-Large-Category : UUω
  is-initial-obj-Large-Category =
    is-initial-obj-Large-Precategory (large-precategory-Large-Category C) X
```
