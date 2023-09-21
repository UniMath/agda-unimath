# Initial objects in a precategory

```agda
module category-theory.initial-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The **initial object** of a [precategory](category-theory.precategories.md), if
it exists, is an object with the universal property that there is a
[unique](foundation-core.contractible-types.md) morphism from it to any object.

## Definitions

### The universal property of an initial object in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (x : obj-Precategory C)
  where

  is-initial-prop-obj-Precategory : Prop (l1 ⊔ l2)
  is-initial-prop-obj-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ y → is-contr-Prop (hom-Precategory C x y))

  is-initial-obj-Precategory : UU (l1 ⊔ l2)
  is-initial-obj-Precategory = type-Prop is-initial-prop-obj-Precategory

  is-prop-is-initial-obj-Precategory : is-prop is-initial-obj-Precategory
  is-prop-is-initial-obj-Precategory =
    is-prop-type-Prop is-initial-prop-obj-Precategory

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x : obj-Precategory C)
  (t : is-initial-obj-Precategory C x)
  where

  hom-is-initial-obj-Precategory :
    (y : obj-Precategory C) →
    hom-Precategory C x y
  hom-is-initial-obj-Precategory = center ∘ t

  is-unique-hom-is-initial-obj-Precategory :
    (y : obj-Precategory C) →
    (f : hom-Precategory C x y) →
    hom-is-initial-obj-Precategory y ＝ f
  is-unique-hom-is-initial-obj-Precategory = contraction ∘ t
```

### Initial objects in precategories

```agda
initial-obj-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
initial-obj-Precategory C =
  Σ (obj-Precategory C) (is-initial-obj-Precategory C)

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (t : initial-obj-Precategory C)
  where

  obj-initial-obj-Precategory : obj-Precategory C
  obj-initial-obj-Precategory = pr1 t

  is-initial-obj-initial-obj-Precategory :
    is-initial-obj-Precategory C obj-initial-obj-Precategory
  is-initial-obj-initial-obj-Precategory = pr2 t

  hom-initial-obj-Precategory :
    (y : obj-Precategory C) →
    hom-Precategory C obj-initial-obj-Precategory y
  hom-initial-obj-Precategory =
    hom-is-initial-obj-Precategory C
      ( obj-initial-obj-Precategory)
      ( is-initial-obj-initial-obj-Precategory)

  is-unique-hom-initial-obj-Precategory :
    (y : obj-Precategory C) →
    (f : hom-Precategory C obj-initial-obj-Precategory y) →
    hom-initial-obj-Precategory y ＝ f
  is-unique-hom-initial-obj-Precategory =
    is-unique-hom-is-initial-obj-Precategory C
      ( obj-initial-obj-Precategory)
      ( is-initial-obj-initial-obj-Precategory)
```
