# Large categories

```agda
module category-theory.large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **large category** in Homotopy Type Theory is a
[large precategory](category-theory.large-precategories.md) for which the
[identities](foundation-core.identity-types.md) between the objects are the
[isomorphisms](category-theory.isomorphisms-in-large-categories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A large precategory is a large category if this function is
an equivalence. Note that being a large category is a
[proposition](foundation-core.propositions.md) since `is-equiv` is a
proposition.

## Definition

### The predicate on large precategories of being a large category

```agda
is-large-category-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) → UUω
is-large-category-Large-Precategory C =
  {l : Level} (X Y : obj-Large-Precategory C l) →
  is-equiv (iso-eq-Large-Precategory C X Y)
```

### The large type of large categories

```agda
record
  Large-Category (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  eta-equality

  constructor
    make-Large-Category

  field
    large-precategory-Large-Category :
      Large-Precategory α β

    is-large-category-Large-Category :
      is-large-category-Large-Precategory large-precategory-Large-Category

open Large-Category public
```

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  obj-Large-Category : (l : Level) → UU (α l)
  obj-Large-Category =
    obj-Large-Precategory (large-precategory-Large-Category C)

  hom-set-Large-Category :
    {l1 l2 : Level} →
    obj-Large-Category l1 →
    obj-Large-Category l2 →
    Set (β l1 l2)
  hom-set-Large-Category =
    hom-set-Large-Precategory (large-precategory-Large-Category C)

  hom-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category l1)
    (Y : obj-Large-Category l2) →
    UU (β l1 l2)
  hom-Large-Category X Y = type-Set (hom-set-Large-Category X Y)

  is-set-hom-Large-Category :
    {l1 l2 : Level}
    (X : obj-Large-Category l1)
    (Y : obj-Large-Category l2) →
    is-set (hom-Large-Category X Y)
  is-set-hom-Large-Category X Y =
    is-set-type-Set (hom-set-Large-Category X Y)

  comp-hom-Large-Category :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3} →
    hom-Large-Category Y Z →
    hom-Large-Category X Y →
    hom-Large-Category X Z
  comp-hom-Large-Category =
    comp-hom-Large-Precategory (large-precategory-Large-Category C)

  id-hom-Large-Category :
    {l1 : Level} {X : obj-Large-Category l1} →
    hom-Large-Category X X
  id-hom-Large-Category =
    id-hom-Large-Precategory (large-precategory-Large-Category C)

  involutive-eq-associative-comp-hom-Large-Category :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {W : obj-Large-Category l4} →
    (h : hom-Large-Category Z W)
    (g : hom-Large-Category Y Z)
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category (comp-hom-Large-Category h g) f) ＝ⁱ
    ( comp-hom-Large-Category h (comp-hom-Large-Category g f))
  involutive-eq-associative-comp-hom-Large-Category =
    involutive-eq-associative-comp-hom-Large-Precategory
      ( large-precategory-Large-Category C)

  associative-comp-hom-Large-Category :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {W : obj-Large-Category l4} →
    (h : hom-Large-Category Z W)
    (g : hom-Large-Category Y Z)
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category (comp-hom-Large-Category h g) f) ＝
    ( comp-hom-Large-Category h (comp-hom-Large-Category g f))
  associative-comp-hom-Large-Category =
    associative-comp-hom-Large-Precategory (large-precategory-Large-Category C)

  left-unit-law-comp-hom-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category id-hom-Large-Category f) ＝ f
  left-unit-law-comp-hom-Large-Category =
    left-unit-law-comp-hom-Large-Precategory
      ( large-precategory-Large-Category C)

  right-unit-law-comp-hom-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    (f : hom-Large-Category X Y) →
    ( comp-hom-Large-Category f id-hom-Large-Category) ＝ f
  right-unit-law-comp-hom-Large-Category =
    right-unit-law-comp-hom-Large-Precategory
      ( large-precategory-Large-Category C)

  ap-comp-hom-Large-Category :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3}
    {g g' : hom-Large-Category Y Z} (p : g ＝ g')
    {f f' : hom-Large-Category X Y} (q : f ＝ f') →
    comp-hom-Large-Category g f ＝ comp-hom-Large-Category g' f'
  ap-comp-hom-Large-Category p q =
    ap-binary comp-hom-Large-Category p q

  comp-hom-Large-Category' :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category l1}
    {Y : obj-Large-Category l2}
    {Z : obj-Large-Category l3} →
    hom-Large-Category X Y →
    hom-Large-Category Y Z →
    hom-Large-Category X Z
  comp-hom-Large-Category' f g = comp-hom-Large-Category g f
```

### Categories obtained from large categories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  (is-large-category-C : is-large-category-Large-Precategory C)
  where

  is-category-is-large-category-Large-Precategory :
    (l : Level) → is-category-Precategory (precategory-Large-Precategory C l)
  is-category-is-large-category-Large-Precategory l X Y =
    is-equiv-htpy
      ( iso-eq-Large-Precategory C X Y)
      ( compute-iso-eq-Large-Precategory C X Y)
      ( is-large-category-C X Y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  precategory-Large-Category : (l : Level) → Precategory (α l) (β l l)
  precategory-Large-Category =
    precategory-Large-Precategory (large-precategory-Large-Category C)

  is-category-Large-Category :
    (l : Level) → is-category-Precategory (precategory-Large-Category l)
  is-category-Large-Category =
    is-category-is-large-category-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-large-category-Large-Category C)

  category-Large-Category : (l : Level) → Category (α l) (β l l)
  pr1 (category-Large-Category l) = precategory-Large-Category l
  pr2 (category-Large-Category l) = is-category-Large-Category l
```

### Equalities induce morphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  {l1 : Level} (X Y : obj-Large-Category C l1)
  where

  hom-eq-Large-Category : X ＝ Y → hom-Large-Category C X Y
  hom-eq-Large-Category =
    hom-eq-Large-Precategory (large-precategory-Large-Category C) X Y

  hom-inv-eq-Large-Category : X ＝ Y → hom-Large-Category C Y X
  hom-inv-eq-Large-Category =
    hom-inv-eq-Large-Precategory (large-precategory-Large-Category C) X Y

  compute-hom-eq-Large-Category :
    hom-eq-Category (category-Large-Category C l1) X Y ~ hom-eq-Large-Category
  compute-hom-eq-Large-Category =
    compute-hom-eq-Large-Precategory (large-precategory-Large-Category C) X Y
```

### Pre- and postcomposing by a morphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  {l1 l2 l3 : Level}
  where

  precomp-hom-Large-Category :
    {X : obj-Large-Category C l1}
    {Y : obj-Large-Category C l2}
    (f : hom-Large-Category C X Y) →
    (Z : obj-Large-Category C l3) →
    hom-Large-Category C Y Z → hom-Large-Category C X Z
  precomp-hom-Large-Category f Z g =
    comp-hom-Large-Category C g f

  postcomp-hom-Large-Category :
    (X : obj-Large-Category C l1)
    {Y : obj-Large-Category C l2}
    {Z : obj-Large-Category C l3}
    (f : hom-Large-Category C Y Z) →
    hom-Large-Category C X Y → hom-Large-Category C X Z
  postcomp-hom-Large-Category X f g =
    comp-hom-Large-Category C f g
```
