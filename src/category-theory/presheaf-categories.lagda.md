# Presheaf categories

```agda
module category-theory.presheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.copresheaf-categories
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.category-of-sets
open import foundation.commuting-squares-of-maps
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
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

  presheaf-large-precategory-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-large-precategory-Precategory =
    copresheaf-large-precategory-Precategory (opposite-Precategory C)

  is-large-category-presheaf-large-category-Precategory :
    is-large-category-Large-Precategory presheaf-large-precategory-Precategory
  is-large-category-presheaf-large-category-Precategory =
    is-large-category-copresheaf-large-category-Precategory
      ( opposite-Precategory C)

  presheaf-large-category-Precategory :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-large-category-Precategory =
    copresheaf-large-category-Precategory (opposite-Precategory C)

  presheaf-Precategory : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  presheaf-Precategory =
    obj-Large-Category presheaf-large-category-Precategory

  module _
    {l3 : Level} (P : presheaf-Precategory l3)
    where

    element-set-presheaf-Precategory : obj-Precategory C → Set l3
    element-set-presheaf-Precategory =
      obj-functor-Small-Large-Precategory
        ( opposite-Precategory C)
        ( Set-Large-Precategory)
        ( P)

    element-presheaf-Precategory : obj-Precategory C → UU l3
    element-presheaf-Precategory X =
      type-Set (element-set-presheaf-Precategory X)

    action-presheaf-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      element-presheaf-Precategory Y → element-presheaf-Precategory X
    action-presheaf-Precategory =
      hom-functor-Small-Large-Precategory
        ( opposite-Precategory C)
        ( Set-Large-Precategory)
        ( P)

    preserves-id-action-presheaf-Precategory :
      {X : obj-Precategory C} →
      action-presheaf-Precategory {X} {X} (id-hom-Precategory C) ~ id
    preserves-id-action-presheaf-Precategory =
      htpy-eq
        ( preserves-id-functor-Small-Large-Precategory
          ( opposite-Precategory C)
          ( Set-Large-Precategory)
          ( P)
          ( _))

    preserves-comp-action-presheaf-Precategory :
      {X Y Z : obj-Precategory C}
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      action-presheaf-Precategory (comp-hom-Precategory C g f) ~
      action-presheaf-Precategory f ∘ action-presheaf-Precategory g
    preserves-comp-action-presheaf-Precategory g f =
      htpy-eq
        ( preserves-comp-functor-Small-Large-Precategory
          ( opposite-Precategory C)
          ( Set-Large-Precategory)
          ( P)
          ( f)
          ( g))

  hom-set-presheaf-Precategory :
    {l3 l4 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4) → Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-presheaf-Precategory =
    hom-set-Large-Category presheaf-large-category-Precategory

  hom-presheaf-Precategory :
    {l3 l4 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-presheaf-Precategory =
    hom-Large-Category presheaf-large-category-Precategory

  module _
    {l3 l4 : Level}
    (P : presheaf-Precategory l3) (Q : presheaf-Precategory l4)
    (h : hom-presheaf-Precategory P Q)
    where

    map-hom-presheaf-Precategory :
      (X : obj-Precategory C) →
      element-presheaf-Precategory P X → element-presheaf-Precategory Q X
    map-hom-presheaf-Precategory =
      hom-natural-transformation-Small-Large-Precategory
        ( opposite-Precategory C)
        ( Set-Large-Precategory)
        ( P)
        ( Q)
        ( h)

    naturality-hom-presheaf-Precategory :
      {X Y : obj-Precategory C} (f : hom-Precategory C X Y) →
      coherence-square-maps
        ( action-presheaf-Precategory P f)
        ( map-hom-presheaf-Precategory Y)
        ( map-hom-presheaf-Precategory X)
        ( action-presheaf-Precategory Q f)
    naturality-hom-presheaf-Precategory f =
      htpy-eq
        ( naturality-natural-transformation-Small-Large-Precategory
          ( opposite-Precategory C)
          ( Set-Large-Precategory)
          ( P)
          ( Q)
          ( h)
          ( f))

  comp-hom-presheaf-Precategory :
    {l3 l4 l5 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4)
    (Z : presheaf-Precategory l5) →
    hom-presheaf-Precategory Y Z → hom-presheaf-Precategory X Y →
    hom-presheaf-Precategory X Z
  comp-hom-presheaf-Precategory X Y Z =
    comp-hom-Large-Category presheaf-large-category-Precategory {X = X} {Y} {Z}

  id-hom-presheaf-Precategory :
    {l3 : Level} (X : presheaf-Precategory l3) →
    hom-presheaf-Precategory X X
  id-hom-presheaf-Precategory {l3} X =
    id-hom-Large-Category presheaf-large-category-Precategory {l3} {X}

  associative-comp-hom-presheaf-Precategory :
    {l3 l4 l5 l6 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4)
    (Z : presheaf-Precategory l5)
    (W : presheaf-Precategory l6)
    (h : hom-presheaf-Precategory Z W)
    (g : hom-presheaf-Precategory Y Z)
    (f : hom-presheaf-Precategory X Y) →
    comp-hom-presheaf-Precategory X Y W
      ( comp-hom-presheaf-Precategory Y Z W h g)
      ( f) ＝
    comp-hom-presheaf-Precategory X Z W h
      ( comp-hom-presheaf-Precategory X Y Z g f)
  associative-comp-hom-presheaf-Precategory X Y Z W =
    associative-comp-hom-Large-Category
      ( presheaf-large-category-Precategory)
      { X = X}
      { Y}
      { Z}
      { W}

  involutive-eq-associative-comp-hom-presheaf-Precategory :
    {l3 l4 l5 l6 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4)
    (Z : presheaf-Precategory l5)
    (W : presheaf-Precategory l6)
    (h : hom-presheaf-Precategory Z W)
    (g : hom-presheaf-Precategory Y Z)
    (f : hom-presheaf-Precategory X Y) →
    comp-hom-presheaf-Precategory X Y W
      ( comp-hom-presheaf-Precategory Y Z W h g)
      ( f) ＝ⁱ
    comp-hom-presheaf-Precategory X Z W h
      ( comp-hom-presheaf-Precategory X Y Z g f)
  involutive-eq-associative-comp-hom-presheaf-Precategory X Y Z W =
    involutive-eq-associative-comp-hom-Large-Category
      ( presheaf-large-category-Precategory)
      { X = X}
      { Y}
      { Z}
      { W}

  left-unit-law-comp-hom-presheaf-Precategory :
    {l3 l4 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4)
    (f : hom-presheaf-Precategory X Y) →
    comp-hom-presheaf-Precategory X Y Y
      ( id-hom-presheaf-Precategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-presheaf-Precategory X Y =
    left-unit-law-comp-hom-Large-Category
      ( presheaf-large-category-Precategory)
      { X = X}
      { Y}

  right-unit-law-comp-hom-presheaf-Precategory :
    {l3 l4 : Level}
    (X : presheaf-Precategory l3)
    (Y : presheaf-Precategory l4)
    (f : hom-presheaf-Precategory X Y) →
    comp-hom-presheaf-Precategory X X Y f
      ( id-hom-presheaf-Precategory X) ＝
    f
  right-unit-law-comp-hom-presheaf-Precategory X Y =
    right-unit-law-comp-hom-Large-Category
      ( presheaf-large-category-Precategory)
      { X = X}
      { Y}
```

### The category of small presheaves on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (l : Level)
  where

  presheaf-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  presheaf-precategory-Precategory =
    precategory-Large-Category (presheaf-large-category-Precategory C) l

  presheaf-category-Precategory : Category (l1 ⊔ l2 ⊔ lsuc l) (l1 ⊔ l2 ⊔ l)
  presheaf-category-Precategory =
    category-Large-Category (presheaf-large-category-Precategory C) l
```

## See also

- [The Yoneda lemma](category-theory.yoneda-lemma-precategories.md)

## External links

- [Presheaf precategories](https://1lab.dev/Cat.Functor.Base.html#presheaf-precategories)
  at 1lab
- [category of presheaves](https://ncatlab.org/nlab/show/category+of+presheaves)
  at $n$Lab
- [presheaf](https://ncatlab.org/nlab/show/presheaf) at $n$Lab
