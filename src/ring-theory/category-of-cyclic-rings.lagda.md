# The category of cyclic rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.category-of-cyclic-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.full-large-subprecategories funext univalence truncations
open import category-theory.large-categories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations

open import foundation.universe-levels

open import order-theory.large-posets funext univalence truncations

open import ring-theory.category-of-rings funext univalence truncations
open import ring-theory.cyclic-rings funext univalence truncations
open import ring-theory.homomorphisms-cyclic-rings funext univalence truncations
open import ring-theory.precategory-of-rings funext univalence truncations
```

</details>

## Idea

The
{{#concept "large category of cyclic rings" Agda=Cyclic-Ring-Large-Category}} is
the [large category](category-theory.large-categories.md) consisting of
[cyclic rings](ring-theory.cyclic-rings.md) and
[ring homomorphisms](ring-theory.homomorphisms-cyclic-rings.md).

Note that we already showed that there is at most one ring homomorphism between
any two cyclic rings, so it follows that the large category of cyclic rings is
in fact a [large poset](order-theory.large-posets.md). The large poset of cyclic
rings is constructed in the file
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.md).

## Definition

### The precategory of cyclic rings as a full subprecategory of the precategory of rings

```agda
Cyclic-Ring-Full-Large-Subprecategory :
  Full-Large-Subprecategory (λ l → l) Ring-Large-Precategory
Cyclic-Ring-Full-Large-Subprecategory = is-cyclic-prop-Ring
```

### The large precategory of cyclic rings

```agda
Cyclic-Ring-Large-Precategory : Large-Precategory lsuc (_⊔_)
Cyclic-Ring-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Ring-Large-Precategory)
    ( Cyclic-Ring-Full-Large-Subprecategory)
```

### The large category of cyclic rings

```agda
abstract
  is-large-category-Cyclic-Ring-Large-Category :
    is-large-category-Large-Precategory Cyclic-Ring-Large-Precategory
  is-large-category-Cyclic-Ring-Large-Category =
    is-large-category-large-precategory-is-large-category-Full-Large-Subprecategory
      ( Ring-Large-Precategory)
      ( Cyclic-Ring-Full-Large-Subprecategory)
      ( is-large-category-Ring-Large-Category)

Cyclic-Ring-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category
  Cyclic-Ring-Large-Category =
  Cyclic-Ring-Large-Precategory
is-large-category-Large-Category
  Cyclic-Ring-Large-Category =
  is-large-category-Cyclic-Ring-Large-Category
```

### The small categories of cyclic rings

```agda
Cyclic-Ring-Category : (l : Level) → Category (lsuc l) l
Cyclic-Ring-Category = category-Large-Category Cyclic-Ring-Large-Category
```

## Properties

### The large category of cyclic rings is a large poset

```agda
is-large-poset-Cyclic-Ring-Large-Category :
  is-large-poset-Large-Category Cyclic-Ring-Large-Category
is-large-poset-Cyclic-Ring-Large-Category =
  is-prop-hom-Cyclic-Ring
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
