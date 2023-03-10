# Initial objects of a precategory

```agda
module category-theory.initial-objects-precategories where
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

The initial object of a precategory (if it exists) is an object with the universal property that there is a unique morphism from it to any object.

## Definition

```agda
initial-object : {l1 l2 : Level} (C : Precat l1 l2) → UU (l1 ⊔ l2)
initial-object C =
  Σ (obj-Precat C) λ i →
    (x : obj-Precat C) → is-contr (type-hom-Precat C i x)

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (i : initial-object C) where

  object-initial-object : obj-Precat C
  object-initial-object = pr1 i

  morphism-initial-object :
    (x : obj-Precat C) →
    type-hom-Precat C object-initial-object x
  morphism-initial-object x = pr1 (pr2 i x)

  is-unique-morphism-initial-object :
    (x : obj-Precat C) (f : type-hom-Precat C object-initial-object x) →
    morphism-initial-object x ＝ f
  is-unique-morphism-initial-object x = pr2 (pr2 i x)
```
