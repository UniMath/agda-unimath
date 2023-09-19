# Full large subprecategories

```agda
module category-theory.large-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **full large subprecategory** of a [large precategory](category-theory.large-precategories.md) `C` consists of a family of [subtypes](foundation.subtypes.md) of the types `obj-Large-Precategory C l` for each universe level `l`.

Alternatively, we say that a [large subcategory](category-theory.large-subcategory.md) **is full** if for every two objects `X` and `Y` in the subcategory, the subtype of homomorphisms from `X` to `Y` in the subcategory is [full](foundation.full-subtypes.md).

Note that large full subprecategories are not assumed to be closed under isomorphisms.

## Definitions

### Large subprecategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (C : Large-Precategory α β)
  where

  Large-Subprecategory : UUω
  Large-Subprecategory = (l : Level) → subtype (γ l) (obj-Large-Precategory C l)

  module _
    (P : Large-Subprecategory)
    where

    is-in-Large-Subprecategory :
      {l : Level} (X : obj-Large-Precategory C l) → UU (γ l)
    is-in-Large-Subprecategory X = is-in-subtype (P _) X

    obj-Large-Subprecategory : (l : Level) → UU (α l ⊔ γ l)
    obj-Large-Subprecategory l = type-subtype (P l)

    hom-Large-Subprecategory :
      {l1 l2 : Level}
      (X : obj-Large-Subprecategory l1)
      (Y : obj-Large-Subprecategory l2) →
      Set {!!}
    hom-Large-Subprecategory = {!!}
```

## Properties

### A large subprecategory of a large category is a large category
