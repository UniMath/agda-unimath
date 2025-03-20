# Full large subprecategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.full-large-subprecategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories funext
open import category-theory.isomorphisms-in-large-categories funext
open import category-theory.isomorphisms-in-large-precategories funext
open import category-theory.large-categories funext
open import category-theory.large-precategories funext

open import foundation.function-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.subtype-identity-principle
open import foundation.subtypes funext
open import foundation.universe-levels
```

</details>

## Idea

A **full large subprecategory** of a
[large precategory](category-theory.large-precategories.md) `C` consists of a
family of [subtypes](foundation.subtypes.md) of the types
`obj-Large-Precategory C l` for each universe level `l`.

Alternatively, we say that a
[large subcategory](category-theory.large-subcategories.md) **is full** if for
every two objects `X` and `Y` in the subcategory, the subtype of morphisms from
`X` to `Y` in the subcategory is [full](foundation.full-subtypes.md).

Note that full large subprecategories are not assumed to be closed under
isomorphisms.

## Definitions

### Full large subprecategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (C : Large-Precategory α β)
  where

  Full-Large-Subprecategory : UUω
  Full-Large-Subprecategory =
    {l : Level} → subtype (γ l) (obj-Large-Precategory C l)

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Precategory α β)
  (P : Full-Large-Subprecategory γ C)
  where

  is-in-obj-Full-Large-Subprecategory :
    {l : Level} (X : obj-Large-Precategory C l) → UU (γ l)
  is-in-obj-Full-Large-Subprecategory X = is-in-subtype P X

  is-prop-is-in-obj-Full-Large-Subprecategory :
    {l : Level} (X : obj-Large-Precategory C l) →
    is-prop (is-in-obj-Full-Large-Subprecategory X)
  is-prop-is-in-obj-Full-Large-Subprecategory =
    is-prop-is-in-subtype P

  obj-Full-Large-Subprecategory : (l : Level) → UU (α l ⊔ γ l)
  obj-Full-Large-Subprecategory l = type-subtype (P {l})

  hom-set-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2) →
    Set (β l1 l2)
  hom-set-Full-Large-Subprecategory X Y =
    hom-set-Large-Precategory C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)

  hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2) →
    UU (β l1 l2)
  hom-Full-Large-Subprecategory X Y =
    hom-Large-Precategory C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)

  comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3) →
    hom-Full-Large-Subprecategory Y Z → hom-Full-Large-Subprecategory X Y →
    hom-Full-Large-Subprecategory X Z
  comp-hom-Full-Large-Subprecategory X Y Z =
    comp-hom-Large-Precategory C

  id-hom-Full-Large-Subprecategory :
    {l1 : Level} (X : obj-Full-Large-Subprecategory l1) →
    hom-Full-Large-Subprecategory X X
  id-hom-Full-Large-Subprecategory X =
    id-hom-Large-Precategory C

  associative-comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3)
    (W : obj-Full-Large-Subprecategory l4)
    (h : hom-Full-Large-Subprecategory Z W)
    (g : hom-Full-Large-Subprecategory Y Z)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y W
      ( comp-hom-Full-Large-Subprecategory Y Z W h g)
      ( f) ＝
    comp-hom-Full-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Full-Large-Subprecategory X Y Z g f)
  associative-comp-hom-Full-Large-Subprecategory X Y Z W =
    associative-comp-hom-Large-Precategory C

  involutive-eq-associative-comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3)
    (W : obj-Full-Large-Subprecategory l4)
    (h : hom-Full-Large-Subprecategory Z W)
    (g : hom-Full-Large-Subprecategory Y Z)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y W
      ( comp-hom-Full-Large-Subprecategory Y Z W h g)
      ( f) ＝ⁱ
    comp-hom-Full-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Full-Large-Subprecategory X Y Z g f)
  involutive-eq-associative-comp-hom-Full-Large-Subprecategory X Y Z W =
    involutive-eq-associative-comp-hom-Large-Precategory C

  left-unit-law-comp-hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y Y
      ( id-hom-Full-Large-Subprecategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Large-Subprecategory X Y =
    left-unit-law-comp-hom-Large-Precategory C

  right-unit-law-comp-hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X X Y
      ( f)
      ( id-hom-Full-Large-Subprecategory X) ＝
    f
  right-unit-law-comp-hom-Full-Large-Subprecategory X Y =
    right-unit-law-comp-hom-Large-Precategory C

  large-precategory-Full-Large-Subprecategory :
    Large-Precategory (λ l → α l ⊔ γ l) β
  obj-Large-Precategory
    large-precategory-Full-Large-Subprecategory =
    obj-Full-Large-Subprecategory
  hom-set-Large-Precategory
    large-precategory-Full-Large-Subprecategory =
    hom-set-Full-Large-Subprecategory
  comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory
    {l1} {l2} {l3} {X} {Y} {Z} =
    comp-hom-Full-Large-Subprecategory X Y Z
  id-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {X} =
    id-hom-Full-Large-Subprecategory X
  involutive-eq-associative-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory
    {l1} {l2} {l3} {l4} {X} {Y} {Z} {W} =
    involutive-eq-associative-comp-hom-Full-Large-Subprecategory X Y Z W
  left-unit-law-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {l2} {X} {Y} =
    left-unit-law-comp-hom-Full-Large-Subprecategory X Y
  right-unit-law-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {l2} {X} {Y} =
    right-unit-law-comp-hom-Full-Large-Subprecategory X Y

  iso-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2) →
    UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Full-Large-Subprecategory X Y =
    iso-Large-Precategory C (inclusion-subtype P X) (inclusion-subtype P Y)

  iso-eq-Full-Large-Subprecategory :
    {l1 : Level} (X Y : obj-Full-Large-Subprecategory l1) →
    (X ＝ Y) → iso-Full-Large-Subprecategory X Y
  iso-eq-Full-Large-Subprecategory =
    iso-eq-Large-Precategory large-precategory-Full-Large-Subprecategory
```

### The forgetful functor from a full large subprecategory to the ambient large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Precategory α β)
  (P : Full-Large-Subprecategory γ C)
  where

  forgetful-functor-Full-Large-Subprecategory :
    functor-Large-Precategory
      ( λ l → l)
      ( large-precategory-Full-Large-Subprecategory C P)
      ( C)
  obj-functor-Large-Precategory
    forgetful-functor-Full-Large-Subprecategory =
    inclusion-subtype P
  hom-functor-Large-Precategory
    forgetful-functor-Full-Large-Subprecategory =
    id
  preserves-comp-functor-Large-Precategory
    forgetful-functor-Full-Large-Subprecategory g f =
    refl
  preserves-id-functor-Large-Precategory
    forgetful-functor-Full-Large-Subprecategory =
    refl
```

## Properties

### A full large subprecategory of a large category is a large category

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Precategory α β)
  (P : Full-Large-Subprecategory γ C)
  where

  is-large-category-large-precategory-is-large-category-Full-Large-Subprecategory :
    is-large-category-Large-Precategory C →
    is-large-category-Large-Precategory
      ( large-precategory-Full-Large-Subprecategory C P)
  is-large-category-large-precategory-is-large-category-Full-Large-Subprecategory
    is-large-category-C X =
    fundamental-theorem-id
      ( is-torsorial-Eq-subtype
        ( is-torsorial-iso-Large-Category
          ( make-Large-Category C is-large-category-C)
          ( inclusion-subtype P X))
        ( is-prop-is-in-subtype P)
        ( inclusion-subtype P X)
        ( id-iso-Large-Precategory C)
        ( is-in-subtype-inclusion-subtype P X))
      ( iso-eq-Full-Large-Subprecategory C P X)
```
