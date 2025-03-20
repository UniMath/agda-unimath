# The category of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.category-of-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.full-large-subcategories funext
open import category-theory.functors-large-categories funext
open import category-theory.large-categories funext
open import category-theory.large-precategories funext
open import category-theory.precategories funext

open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.category-of-groups funext
```

</details>

## Idea

The **category of abelian groups** is the
[full large subcategory](category-theory.full-large-subcategories.md) of the
[category of groups](group-theory.category-of-groups.md) consisting of
[groups](group-theory.groups.md) of which the group operation is
[commutative](group-theory.abelian-groups.md).

## Definitions

### The large category of abelian groups

```agda
Ab-Large-Category : Large-Category lsuc (_⊔_)
Ab-Large-Category =
  large-category-Full-Large-Subcategory
    ( Group-Large-Category)
    ( is-abelian-prop-Group)
```

### The large precategory of abelian groups

```agda
Ab-Large-Precategory : Large-Precategory lsuc (_⊔_)
Ab-Large-Precategory =
  large-precategory-Large-Category Ab-Large-Category
```

### The category of abelian groups of a given universe level

```agda
Ab-Category : (l : Level) → Category (lsuc l) l
Ab-Category = category-Large-Category Ab-Large-Category
```

### The precategory of abelian groups of a given universe level

```agda
Ab-Precategory : (l : Level) → Precategory (lsuc l) l
Ab-Precategory = precategory-Large-Category Ab-Large-Category
```

### The forgetful functor from abelian groups to groups

```agda
forgetful-functor-Ab :
  functor-Large-Category (λ l → l) Ab-Large-Category Group-Large-Category
forgetful-functor-Ab =
  forgetful-functor-Full-Large-Subcategory
    ( Group-Large-Category)
    ( is-abelian-prop-Group)
```
