# The orbit category of a group

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.category-of-orbits-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.full-large-subcategories funext
open import category-theory.isomorphisms-in-large-precategories funext
open import category-theory.large-categories funext
open import category-theory.large-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import group-theory.category-of-group-actions funext
open import group-theory.group-actions funext
open import group-theory.groups funext
open import group-theory.homomorphisms-group-actions funext
open import group-theory.isomorphisms-group-actions funext
open import group-theory.precategory-of-group-actions funext
open import group-theory.transitive-group-actions funext
```

</details>

## Idea

The **orbit category of a group** `𝒪(G)` is the
[full subcategory](category-theory.full-large-subcategories.md) of the
[category of `G`-sets](group-theory.category-of-group-actions.md) consisting of
orbits of `G`, i.e. [transitive](group-theory.transitive-group-actions.md)
[`G`-sets](group-theory.group-actions.md). Equivalently, an orbit of `G` is a
`G`-set that is
[merely equivalent](group-theory.mere-equivalences-group-actions.md) to a
quotient `G`-set `G/H` for some [subgroup](group-theory.subgroups.md) `H`.

## Definitions

### The large orbit category of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Full-Large-Subcategory :
    Full-Large-Subcategory (l1 ⊔_) (action-Group-Large-Category G)
  orbit-Group-Full-Large-Subcategory = is-transitive-prop-action-Group G

  orbit-Group-Large-Category :
    Large-Category (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  orbit-Group-Large-Category =
    large-category-Full-Large-Subcategory
      ( action-Group-Large-Category G)
      ( orbit-Group-Full-Large-Subcategory)
```

### The large orbit precategory of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  orbit-Group-Large-Precategory =
    large-precategory-Large-Category (orbit-Group-Large-Category G)
```

### The small orbit category of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Category : (l2 : Level) → Category (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  orbit-Group-Category = category-Large-Category (orbit-Group-Large-Category G)
```

### The small orbit precategory of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Precategory : (l2 : Level) → Precategory (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  orbit-Group-Precategory =
    precategory-Large-Category (orbit-Group-Large-Category G)
```

## External links

- [orbit category](https://ncatlab.org/nlab/show/orbit+category) at $n$Lab
