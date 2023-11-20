# Presheaf categories

```agda
module category-theory.presheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.copresheaf-categories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, we can form its
**presheaf [category](category-theory.large-categories.md)** as the
[large category of functors](category-theory.functors-from-small-to-large-precategories.md)
from the [opposite of](category-theory.opposite-precategories.md) `C`, `Cᵒᵖ`,
into the [large category of sets](foundation.category-of-sets.md)

```text
  Cᵒᵖ → Set.
```

To this large category, there is an associated
[small category](category-theory.categories.md) of small presheaves, taking
values in small [sets](foundation-core.sets.md).

## Definitions

### The large category of presheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  presheaf-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-Large-Precategory =
    copresheaf-Large-Precategory (opposite-Precategory C)

  is-large-category-presheaf-Large-Category :
    is-large-category-Large-Precategory presheaf-Large-Precategory
  is-large-category-presheaf-Large-Category =
    is-large-category-copresheaf-Large-Category (opposite-Precategory C)

  presheaf-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-Large-Category = copresheaf-Large-Category (opposite-Precategory C)

  obj-presheaf-Large-Category : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  obj-presheaf-Large-Category =
    obj-Large-Precategory presheaf-Large-Precategory

  hom-set-presheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4) → Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-presheaf-Large-Category =
    hom-set-Large-Precategory presheaf-Large-Precategory

  hom-presheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-presheaf-Large-Category =
    hom-Large-Precategory presheaf-Large-Precategory

  comp-hom-presheaf-Large-Category :
    {l3 l4 l5 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4)
    (Z : obj-presheaf-Large-Category l5) →
    hom-presheaf-Large-Category Y Z → hom-presheaf-Large-Category X Y →
    hom-presheaf-Large-Category X Z
  comp-hom-presheaf-Large-Category X Y Z =
    comp-hom-Large-Precategory presheaf-Large-Precategory {X = X} {Y} {Z}

  id-hom-presheaf-Large-Category :
    {l3 : Level} (X : obj-presheaf-Large-Category l3) →
    hom-presheaf-Large-Category X X
  id-hom-presheaf-Large-Category {l3} X =
    id-hom-Large-Precategory presheaf-Large-Precategory {l3} {X}

  associative-comp-hom-presheaf-Large-Category :
    {l3 l4 l5 l6 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4)
    (Z : obj-presheaf-Large-Category l5)
    (W : obj-presheaf-Large-Category l6)
    (h : hom-presheaf-Large-Category Z W)
    (g : hom-presheaf-Large-Category Y Z)
    (f : hom-presheaf-Large-Category X Y) →
    comp-hom-presheaf-Large-Category X Y W
      ( comp-hom-presheaf-Large-Category Y Z W h g)
      ( f) ＝
    comp-hom-presheaf-Large-Category X Z W h
      ( comp-hom-presheaf-Large-Category X Y Z g f)
  associative-comp-hom-presheaf-Large-Category X Y Z W =
    associative-comp-hom-Large-Precategory
      ( presheaf-Large-Precategory)
      { X = X}
      { Y}
      { Z}
      { W}

  left-unit-law-comp-hom-presheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4)
    (f : hom-presheaf-Large-Category X Y) →
    comp-hom-presheaf-Large-Category X Y Y
      ( id-hom-presheaf-Large-Category Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-presheaf-Large-Category X Y =
    left-unit-law-comp-hom-Large-Precategory
      ( presheaf-Large-Precategory)
      { X = X}
      { Y}

  right-unit-law-comp-hom-presheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-presheaf-Large-Category l3)
    (Y : obj-presheaf-Large-Category l4)
    (f : hom-presheaf-Large-Category X Y) →
    comp-hom-presheaf-Large-Category X X Y f
      ( id-hom-presheaf-Large-Category X) ＝
    f
  right-unit-law-comp-hom-presheaf-Large-Category X Y =
    right-unit-law-comp-hom-Large-Precategory
      ( presheaf-Large-Precategory)
      { X = X}
      { Y}
```

### The category of small presheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  presheaf-Precategory : Precategory (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  presheaf-Precategory =
    precategory-Large-Precategory (presheaf-Large-Precategory C) l

  presheaf-Category : Category (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  presheaf-Category = category-Large-Category (presheaf-Large-Category C) l
```

We also record the components of the category of small presheaves on a
precategory.

```agda
  obj-presheaf-Category =
    obj-Precategory presheaf-Precategory

  hom-set-presheaf-Category =
    hom-set-Precategory presheaf-Precategory

  hom-presheaf-Category =
    hom-Precategory presheaf-Precategory

  comp-hom-presheaf-Category =
    comp-hom-Precategory presheaf-Precategory

  id-hom-presheaf-Category =
    id-hom-Precategory presheaf-Precategory

  associative-comp-hom-presheaf-Category =
    associative-comp-hom-Precategory presheaf-Precategory

  left-unit-law-comp-hom-presheaf-Category =
    left-unit-law-comp-hom-Precategory presheaf-Precategory

  right-unit-law-comp-hom-presheaf-Category =
    right-unit-law-comp-hom-Precategory presheaf-Precategory
```

### Sections of presheaves

As a choice of universe level must be made to talk about sections of presheaves,
this notion coincides for the large and small category of presheaves.

```agda
module _
  {l1 l2 l3 : Level} (C : Precategory l1 l2)
  where

  section-presheaf-Category :
    (F : obj-presheaf-Category C l3) (c : obj-Precategory C) → UU l3
  section-presheaf-Category =
    section-copresheaf-Category (opposite-Precategory C)
```

## See also

- [The Yoneda lemma](category-theory.yoneda-lemma-precategories.md)

## External links

- [Presheaf precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategories)
  at 1lab
- [category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves)
  at $n$Lab
- [presheaf](https://ncatlab.org/nlab/show/presheaf) at $n$Lab
