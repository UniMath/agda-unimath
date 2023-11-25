# Copresheaf categories

```agda
module category-theory.copresheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-functors-from-small-to-large-categories
open import category-theory.functors-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors-from-small-to-large-precategories

open import foundation.category-of-sets
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, we can form its
**copresheaf [category](category-theory.large-categories.md)** as the
[large category of functors](category-theory.functors-from-small-to-large-precategories.md)
from `C`, into the [large category of sets](foundation.category-of-sets.md)

```text
  C → Set.
```

To this large category, there is an associated
[small category](category-theory.categories.md) of small copresheaves, taking
values in small [sets](foundation-core.sets.md).

## Definitions

### The large category of copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  copresheaf-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  copresheaf-Large-Precategory =
    functor-large-precategory-Small-Large-Precategory C Set-Large-Precategory

  is-large-category-copresheaf-Large-Category :
    is-large-category-Large-Precategory copresheaf-Large-Precategory
  is-large-category-copresheaf-Large-Category =
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory
      ( C)
      ( Set-Large-Precategory)
      ( is-large-category-Set-Large-Precategory)

  copresheaf-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  large-precategory-Large-Category copresheaf-Large-Category =
    copresheaf-Large-Precategory
  is-large-category-Large-Category copresheaf-Large-Category =
    is-large-category-copresheaf-Large-Category

  obj-copresheaf-Large-Category : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  obj-copresheaf-Large-Category =
    obj-Large-Precategory copresheaf-Large-Precategory

  hom-set-copresheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4) → Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-copresheaf-Large-Category =
    hom-set-Large-Precategory copresheaf-Large-Precategory

  hom-copresheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-copresheaf-Large-Category =
    hom-Large-Precategory copresheaf-Large-Precategory

  comp-hom-copresheaf-Large-Category :
    {l3 l4 l5 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4)
    (Z : obj-copresheaf-Large-Category l5) →
    hom-copresheaf-Large-Category Y Z → hom-copresheaf-Large-Category X Y →
    hom-copresheaf-Large-Category X Z
  comp-hom-copresheaf-Large-Category X Y Z =
    comp-hom-Large-Precategory copresheaf-Large-Precategory {X = X} {Y} {Z}

  id-hom-copresheaf-Large-Category :
    {l3 : Level} (X : obj-copresheaf-Large-Category l3) →
    hom-copresheaf-Large-Category X X
  id-hom-copresheaf-Large-Category X =
    id-hom-Large-Precategory copresheaf-Large-Precategory {X = X}

  associative-comp-hom-copresheaf-Large-Category :
    {l3 l4 l5 l6 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4)
    (Z : obj-copresheaf-Large-Category l5)
    (W : obj-copresheaf-Large-Category l6)
    (h : hom-copresheaf-Large-Category Z W)
    (g : hom-copresheaf-Large-Category Y Z)
    (f : hom-copresheaf-Large-Category X Y) →
    comp-hom-copresheaf-Large-Category X Y W
      ( comp-hom-copresheaf-Large-Category Y Z W h g)
      ( f) ＝
    comp-hom-copresheaf-Large-Category X Z W
      ( h)
      ( comp-hom-copresheaf-Large-Category X Y Z g f)
  associative-comp-hom-copresheaf-Large-Category X Y Z W =
    associative-comp-hom-Large-Precategory
      ( copresheaf-Large-Precategory)
      { X = X}
      { Y}
      { Z}
      { W}

  left-unit-law-comp-hom-copresheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4)
    (f : hom-copresheaf-Large-Category X Y) →
    comp-hom-copresheaf-Large-Category X Y Y
      ( id-hom-copresheaf-Large-Category Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-copresheaf-Large-Category X Y =
    left-unit-law-comp-hom-Large-Precategory
      ( copresheaf-Large-Precategory)
      { X = X}
      { Y}

  right-unit-law-comp-hom-copresheaf-Large-Category :
    {l3 l4 : Level}
    (X : obj-copresheaf-Large-Category l3)
    (Y : obj-copresheaf-Large-Category l4)
    (f : hom-copresheaf-Large-Category X Y) →
    comp-hom-copresheaf-Large-Category X X Y
      ( f)
      ( id-hom-copresheaf-Large-Category X) ＝
    f
  right-unit-law-comp-hom-copresheaf-Large-Category X Y =
    right-unit-law-comp-hom-Large-Precategory
      ( copresheaf-Large-Precategory)
      { X = X}
      { Y}
```

### The category of small copresheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  copresheaf-Precategory : Precategory (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-Precategory =
    precategory-Large-Precategory (copresheaf-Large-Precategory C) l

  copresheaf-Category : Category (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  copresheaf-Category = category-Large-Category (copresheaf-Large-Category C) l
```

We also record the components of the category of small copresheaves on a
precategory.

```agda
  obj-copresheaf-Category =
    obj-Precategory copresheaf-Precategory

  hom-set-copresheaf-Category =
    hom-set-Precategory copresheaf-Precategory

  hom-copresheaf-Category =
    hom-Precategory copresheaf-Precategory

  comp-hom-copresheaf-Category =
    comp-hom-Precategory copresheaf-Precategory

  id-hom-copresheaf-Category =
    id-hom-Precategory copresheaf-Precategory

  associative-comp-hom-copresheaf-Category =
    associative-comp-hom-Precategory copresheaf-Precategory

  left-unit-law-comp-hom-copresheaf-Category =
    left-unit-law-comp-hom-Precategory copresheaf-Precategory

  right-unit-law-comp-hom-copresheaf-Category =
    right-unit-law-comp-hom-Precategory copresheaf-Precategory
```

### Sections of copresheaves

As a choice of universe level must be made to talk about sections of
copresheaves, this notion coincides for the large and small category of
copresheaves.

```agda
module _
  {l1 l2 l3 : Level} (C : Precategory l1 l2)
  where

  section-copresheaf-Category :
    (F : obj-copresheaf-Category C l3) (c : obj-Precategory C) → UU l3
  section-copresheaf-Category F c =
    type-Set (obj-functor-Precategory C (Set-Precategory l3) F c)
```

## See also

- [The Yoneda lemma](category-theory.yoneda-lemma-precategories.md)

## External links

- [Presheaf precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategories)
  at 1lab
- [category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves)
  at $n$Lab
- [copresheaf](https://ncatlab.org/nlab/show/copresheaf) at $n$Lab
