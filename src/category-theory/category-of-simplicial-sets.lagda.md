# The category of simplicial sets

```agda
module category-theory.category-of-simplicial-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories
open import category-theory.presheaf-categories
open import category-theory.simplex-category

open import foundation.commuting-squares-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "large category of simplicial sets" Agda=sSet-Large-Category}} is
the [presheaf category](category-theory.presheaf-categories.md) on the
[simplex category](category-theory.simplex-category.md)

```text
  Δᵒᵖ → Set.
```

To this large category, there is an associated
[small category](category-theory.categories.md) of **small simplicial sets**,
taking values in small [sets](foundation-core.sets.md).

## Definitions

### The large category of simplicial sets

```agda
sSet-Large-Precategory :
  Large-Precategory lsuc (_⊔_)
sSet-Large-Precategory =
  presheaf-large-precategory-Precategory simplex-Precategory

is-large-category-sSet-Large-Category :
  is-large-category-Large-Precategory sSet-Large-Precategory
is-large-category-sSet-Large-Category =
  is-large-category-presheaf-large-category-Precategory simplex-Precategory

sSet-Large-Category :
  Large-Category lsuc (_⊔_)
sSet-Large-Category =
  presheaf-large-category-Precategory simplex-Precategory

sSet : (l : Level) → UU (lsuc l)
sSet = obj-Large-Category sSet-Large-Category

module _
  {l1 : Level} (X : sSet l1)
  where

  element-set-sSet : obj-simplex-Category → Set l1
  element-set-sSet = element-set-presheaf-Precategory simplex-Precategory X

  element-sSet : obj-simplex-Category → UU l1
  element-sSet X = type-Set (element-set-sSet X)

  action-sSet :
    {X Y : obj-simplex-Category} →
    hom-simplex-Category X Y → element-sSet Y → element-sSet X
  action-sSet = action-presheaf-Precategory simplex-Precategory X

  preserves-id-action-sSet :
    {X : obj-simplex-Category} →
    action-sSet {X} {X} (id-hom-simplex-Category X) ~ id
  preserves-id-action-sSet =
    preserves-id-action-presheaf-Precategory simplex-Precategory X

  preserves-comp-action-sSet :
    {X Y Z : obj-simplex-Category}
    (g : hom-simplex-Category Y Z) (f : hom-simplex-Category X Y) →
    action-sSet (comp-hom-simplex-Category g f) ~
    action-sSet f ∘ action-sSet g
  preserves-comp-action-sSet =
    preserves-comp-action-presheaf-Precategory simplex-Precategory X

hom-set-sSet : {l1 l2 : Level} (X : sSet l1) (Y : sSet l2) → Set (l1 ⊔ l2)
hom-set-sSet = hom-set-Large-Category sSet-Large-Category

hom-sSet : {l1 l2 : Level} (X : sSet l1) (Y : sSet l2) → UU (l1 ⊔ l2)
hom-sSet = hom-Large-Category sSet-Large-Category

module _
  {l1 l2 : Level} (X : sSet l1) (Y : sSet l2) (h : hom-sSet X Y)
  where

  map-hom-sSet :
    (F : obj-simplex-Category) → element-sSet X F → element-sSet Y F
  map-hom-sSet = map-hom-presheaf-Precategory simplex-Precategory X Y h

  naturality-hom-sSet :
    {F E : obj-simplex-Category} (f : hom-simplex-Category F E) →
    coherence-square-maps
      ( action-sSet X f)
      ( map-hom-sSet E)
      ( map-hom-sSet F)
      ( action-sSet Y f)
  naturality-hom-sSet =
    naturality-hom-presheaf-Precategory simplex-Precategory X Y h

comp-hom-sSet :
  {l1 l2 l3 : Level} (X : sSet l1) (Y : sSet l2) (Z : sSet l3) →
  hom-sSet Y Z → hom-sSet X Y → hom-sSet X Z
comp-hom-sSet = comp-hom-presheaf-Precategory simplex-Precategory

id-hom-sSet : {l1 : Level} (X : sSet l1) → hom-sSet X X
id-hom-sSet = id-hom-presheaf-Precategory simplex-Precategory

associative-comp-hom-sSet :
  {l1 l2 l3 l4 : Level}
  (X : sSet l1) (Y : sSet l2) (Z : sSet l3) (W : sSet l4)
  (h : hom-sSet Z W) (g : hom-sSet Y Z) (f : hom-sSet X Y) →
  comp-hom-sSet X Y W (comp-hom-sSet Y Z W h g) f ＝
  comp-hom-sSet X Z W h (comp-hom-sSet X Y Z g f)
associative-comp-hom-sSet =
  associative-comp-hom-presheaf-Precategory simplex-Precategory

involutive-eq-associative-comp-hom-sSet :
  {l1 l2 l3 l4 : Level}
  (X : sSet l1) (Y : sSet l2) (Z : sSet l3) (W : sSet l4)
  (h : hom-sSet Z W) (g : hom-sSet Y Z) (f : hom-sSet X Y) →
  comp-hom-sSet X Y W (comp-hom-sSet Y Z W h g) f ＝ⁱ
  comp-hom-sSet X Z W h (comp-hom-sSet X Y Z g f)
involutive-eq-associative-comp-hom-sSet =
  involutive-eq-associative-comp-hom-presheaf-Precategory simplex-Precategory

left-unit-law-comp-hom-sSet :
  {l1 l2 : Level} (X : sSet l1) (Y : sSet l2) (f : hom-sSet X Y) →
  comp-hom-sSet X Y Y (id-hom-sSet Y) f ＝ f
left-unit-law-comp-hom-sSet =
  left-unit-law-comp-hom-presheaf-Precategory simplex-Precategory

right-unit-law-comp-hom-sSet :
  {l1 l2 : Level} (X : sSet l1) (Y : sSet l2) (f : hom-sSet X Y) →
  comp-hom-sSet X X Y f (id-hom-sSet X) ＝ f
right-unit-law-comp-hom-sSet =
  right-unit-law-comp-hom-presheaf-Precategory simplex-Precategory
```

### The category of small simplicial sets

```agda
sSet-Precategory : (l : Level) → Precategory (lsuc l) l
sSet-Precategory = precategory-Large-Category sSet-Large-Category

sSet-Category : (l : Level) → Category (lsuc l) l
sSet-Category = category-Large-Category sSet-Large-Category
```

## External links

- [simplicial set](https://ncatlab.org/nlab/show/simplicial+set) on $n$Lab
