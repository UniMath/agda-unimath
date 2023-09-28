# Function precategories

```agda
module category-theory.function-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C` and any type `I`,
the function type `I → C` is a precategory consisting of functions taking
`i : I` to an object of `C`. Every component of the structure is given
pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : Precategory l2 l3)
  where

  function-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  function-Precategory = Π-Precategory I (λ _ → C)

  obj-function-Precategory : UU (l1 ⊔ l2)
  obj-function-Precategory = obj-Precategory function-Precategory

  hom-set-function-Precategory :
    obj-function-Precategory → obj-function-Precategory → Set (l1 ⊔ l3)
  hom-set-function-Precategory = hom-set-Precategory function-Precategory

  hom-function-Precategory :
    obj-function-Precategory → obj-function-Precategory → UU (l1 ⊔ l3)
  hom-function-Precategory = hom-Precategory function-Precategory

  comp-hom-function-Precategory :
    {x y z : obj-function-Precategory} →
    hom-function-Precategory y z →
    hom-function-Precategory x y →
    hom-function-Precategory x z
  comp-hom-function-Precategory = comp-hom-Precategory function-Precategory

  associative-comp-hom-function-Precategory :
    {x y z w : obj-function-Precategory}
    (h : hom-function-Precategory z w)
    (g : hom-function-Precategory y z)
    (f : hom-function-Precategory x y) →
    ( comp-hom-function-Precategory (comp-hom-function-Precategory h g) f) ＝
    ( comp-hom-function-Precategory h (comp-hom-function-Precategory g f))
  associative-comp-hom-function-Precategory =
    associative-comp-hom-Precategory function-Precategory

  associative-composition-structure-function-Precategory :
    associative-composition-structure-Set hom-set-function-Precategory
  associative-composition-structure-function-Precategory =
    associative-composition-structure-Precategory function-Precategory

  id-hom-function-Precategory :
    {x : obj-function-Precategory} → hom-function-Precategory x x
  id-hom-function-Precategory = id-hom-Precategory function-Precategory

  left-unit-law-comp-hom-function-Precategory :
    {x y : obj-function-Precategory}
    (f : hom-function-Precategory x y) →
    comp-hom-function-Precategory id-hom-function-Precategory f ＝ f
  left-unit-law-comp-hom-function-Precategory =
    left-unit-law-comp-hom-Precategory function-Precategory

  right-unit-law-comp-hom-function-Precategory :
    {x y : obj-function-Precategory} (f : hom-function-Precategory x y) →
    comp-hom-function-Precategory f id-hom-function-Precategory ＝ f
  right-unit-law-comp-hom-function-Precategory =
    right-unit-law-comp-hom-Precategory function-Precategory

  is-unital-function-Precategory :
    is-unital-composition-structure-Set
      hom-set-function-Precategory
      associative-composition-structure-function-Precategory
  is-unital-function-Precategory =
    is-unital-composition-structure-Precategory function-Precategory
```

### Isomorphisms in the function precategory are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : Precategory l2 l3)
  {x y : obj-function-Precategory I C}
  where

  is-fiberwise-iso-is-iso-function-Precategory :
    (f : hom-function-Precategory I C x y) →
    is-iso-Precategory (function-Precategory I C) f →
    (i : I) → is-iso-Precategory C (f i)
  is-fiberwise-iso-is-iso-function-Precategory =
    is-fiberwise-iso-is-iso-Π-Precategory I (λ _ → C)

  fiberwise-iso-iso-function-Precategory :
    iso-Precategory (function-Precategory I C) x y →
    (i : I) → iso-Precategory C (x i) (y i)
  fiberwise-iso-iso-function-Precategory =
    fiberwise-iso-iso-Π-Precategory I (λ _ → C)

  is-iso-function-is-fiberwise-iso-Precategory :
    (f : hom-function-Precategory I C x y) →
    ((i : I) → is-iso-Precategory C (f i)) →
    is-iso-Precategory (function-Precategory I C) f
  is-iso-function-is-fiberwise-iso-Precategory =
    is-iso-is-fiberwise-iso-Π-Precategory I (λ _ → C)

  iso-function-fiberwise-iso-Precategory :
    ((i : I) → iso-Precategory C (x i) (y i)) →
    iso-Precategory (function-Precategory I C) x y
  iso-function-fiberwise-iso-Precategory =
    iso-fiberwise-iso-Π-Precategory I (λ _ → C)

  is-equiv-is-fiberwise-iso-is-iso-function-Precategory :
    (f : hom-function-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-function-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-function-Precategory =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategory I (λ _ → C)

  equiv-is-fiberwise-iso-is-iso-function-Precategory :
    (f : hom-function-Precategory I C x y) →
    ( is-iso-Precategory (function-Precategory I C) f) ≃
    ( (i : I) → is-iso-Precategory C (f i))
  equiv-is-fiberwise-iso-is-iso-function-Precategory =
    equiv-is-fiberwise-iso-is-iso-Π-Precategory I (λ _ → C)

  is-equiv-is-iso-function-is-fiberwise-iso-Precategory :
    (f : hom-function-Precategory I C x y) →
    is-equiv (is-iso-function-is-fiberwise-iso-Precategory f)
  is-equiv-is-iso-function-is-fiberwise-iso-Precategory =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategory I (λ _ → C)

  equiv-is-iso-function-is-fiberwise-iso-Precategory :
    ( f : hom-function-Precategory I C x y) →
    ( (i : I) → is-iso-Precategory C (f i)) ≃
    ( is-iso-Precategory (function-Precategory I C) f)
  equiv-is-iso-function-is-fiberwise-iso-Precategory =
    equiv-is-iso-is-fiberwise-iso-Π-Precategory I (λ _ → C)

  is-equiv-fiberwise-iso-iso-function-Precategory :
    is-equiv fiberwise-iso-iso-function-Precategory
  is-equiv-fiberwise-iso-iso-function-Precategory =
    is-equiv-fiberwise-iso-iso-Π-Precategory I (λ _ → C)

  equiv-fiberwise-iso-iso-function-Precategory :
    ( iso-Precategory (function-Precategory I C) x y) ≃
    ( (i : I) → iso-Precategory C (x i) (y i))
  equiv-fiberwise-iso-iso-function-Precategory =
    equiv-fiberwise-iso-iso-Π-Precategory I (λ _ → C)

  is-equiv-iso-function-fiberwise-iso-Precategory :
    is-equiv iso-function-fiberwise-iso-Precategory
  is-equiv-iso-function-fiberwise-iso-Precategory =
    is-equiv-iso-fiberwise-iso-Π-Precategory I (λ _ → C)

  equiv-iso-function-fiberwise-iso-Precategory :
    ( (i : I) → iso-Precategory C (x i) (y i)) ≃
    ( iso-Precategory (function-Precategory I C) x y)
  equiv-iso-function-fiberwise-iso-Precategory =
    equiv-iso-fiberwise-iso-Π-Precategory I (λ _ → C)
```
