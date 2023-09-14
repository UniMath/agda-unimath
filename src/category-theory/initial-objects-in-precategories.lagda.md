# Initial objects of a precategory

```agda
module category-theory.initial-objects-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The initial object of a precategory (if it exists) is an object with the
universal property that there is a unique morphism from it to any object.

## Definition

```agda
initial-object-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
initial-object-Precategory C =
  Σ (obj-Precategory C) λ i →
    (x : obj-Precategory C) → is-contr (type-hom-Precategory C i x)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (i : initial-object-Precategory C)
  where

  object-initial-object-Precategory : obj-Precategory C
  object-initial-object-Precategory = pr1 i

  morphism-initial-object-Precategory :
    (x : obj-Precategory C) →
    type-hom-Precategory C object-initial-object-Precategory x
  morphism-initial-object-Precategory x = pr1 (pr2 i x)

  is-unique-morphism-initial-object-Precategory :
    (x : obj-Precategory C)
    (f : type-hom-Precategory C object-initial-object-Precategory x) →
    morphism-initial-object-Precategory x ＝ f
  is-unique-morphism-initial-object-Precategory x = pr2 (pr2 i x)
```
