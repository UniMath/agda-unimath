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
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The **initial object** of a [precategory](category-theory.precategories.md), if
it exists, is an object with the universal property that there is a
[unique](foundation-core.contractible-types.md) morphism from it to any object.

## Definitions

### The predicate of being a initial object in a precategory

```agda
is-initial-obj-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → obj-Precategory C → UU (l1 ⊔ l2)
is-initial-obj-Precategory C x =
  (y : obj-Precategory C) → is-contr (type-hom-Precategory C x y)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x : obj-Precategory C)
  (t : is-initial-obj-Precategory C x)
  where

  hom-is-initial-obj-Precategory :
    (y : obj-Precategory C) →
    type-hom-Precategory C x y
  hom-is-initial-obj-Precategory = center ∘ t

  is-unique-hom-is-initial-obj-Precategory :
    (y : obj-Precategory C) →
    (f : type-hom-Precategory C x y) →
    hom-is-initial-obj-Precategory y ＝ f
  is-unique-hom-is-initial-obj-Precategory = contraction ∘ t

```

### Terminal objects in precategories

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

  is-initial-obj-initial-obj-Precategory : is-initial-obj-Precategory C obj-initial-obj-Precategory
  is-initial-obj-initial-obj-Precategory = pr2 t

  hom-initial-obj-Precategory :
    (y : obj-Precategory C) →
    type-hom-Precategory C obj-initial-obj-Precategory y
  hom-initial-obj-Precategory =
    hom-is-initial-obj-Precategory C
      ( obj-initial-obj-Precategory)
      ( is-initial-obj-initial-obj-Precategory)

  is-unique-hom-initial-obj-Precategory :
    (y : obj-Precategory C) →
    (f : type-hom-Precategory C obj-initial-obj-Precategory y) →
    hom-initial-obj-Precategory y ＝ f
  is-unique-hom-initial-obj-Precategory =
    is-unique-hom-is-initial-obj-Precategory C
      ( obj-initial-obj-Precategory)
      ( is-initial-obj-initial-obj-Precategory)
```
