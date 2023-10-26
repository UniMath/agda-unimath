# Replete subprecategories

```agda
module category-theory.replete-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphism-induction-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.isomorphisms-in-subprecategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A **replete subprecategory** of a [precategory](category-theory.categories.md)
`C` is a [subprecategory](category-theory.subprecategories.md) `P` that is
closed under [isomorphisms](category-theory.isomorphisms-in-precategories.md):

Given an object `x` in `P`, then every isomorphism `f : x ≅ y` in `C`, is
contained in `P`.

## Definitions

### The predicate on a subprecategory of being closed under isomorphic objects

We can define what it means for subprecategories to have objects that are closed
under isomorphisms. Note, however, that this is not yet the correct definition
of a replete subprecategory.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  contains-iso-obj-Subprecategory : UU (l1 ⊔ l2 ⊔ l3)
  contains-iso-obj-Subprecategory =
    (x : obj-Subprecategory C P) (y : obj-Precategory C) →
    iso-Precategory C (inclusion-obj-Subprecategory C P x) y →
    is-in-obj-Subprecategory C P y

  is-prop-contains-iso-obj-Subprecategory :
    is-prop contains-iso-obj-Subprecategory
  is-prop-contains-iso-obj-Subprecategory =
    is-prop-iterated-Π 3 (λ x y f → is-prop-is-in-obj-Subprecategory C P y)

  contains-iso-obj-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 contains-iso-obj-prop-Subprecategory = contains-iso-obj-Subprecategory
  pr2 contains-iso-obj-prop-Subprecategory =
    is-prop-contains-iso-obj-Subprecategory
```

### The predicate of being a replete subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-replete-Subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-replete-Subprecategory =
    (x : obj-Subprecategory C P)
    (y : obj-Precategory C)
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    Σ ( is-in-obj-Subprecategory C P y)
      ( λ y₀ → is-in-iso-obj-subprecategory-Subprecategory C P {x} {y , y₀} f)

  is-prop-is-replete-Subprecategory : is-prop (is-replete-Subprecategory)
  is-prop-is-replete-Subprecategory =
    is-prop-iterated-Π 3
      ( λ x y f →
        is-prop-Σ
          ( is-prop-is-in-obj-Subprecategory C P y)
          ( λ y₀ →
            is-prop-is-in-iso-obj-subprecategory-Subprecategory C P
              { x} {y , y₀} f))

  is-replete-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-replete-prop-Subprecategory = is-replete-Subprecategory
  pr2 is-replete-prop-Subprecategory = is-prop-is-replete-Subprecategory
```

### Replete subprecategories

```agda
Replete-Subprecategory :
  {l1 l2 : Level} (l3 l4 : Level) (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Replete-Subprecategory l3 l4 C =
  Σ (Subprecategory l3 l4 C) (is-replete-Subprecategory C)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Replete-Subprecategory l3 l4 C)
  where

  subprecategory-Replete-Subprecategory : Subprecategory l3 l4 C
  subprecategory-Replete-Subprecategory = pr1 P

  is-replete-Replete-Subprecategory :
    is-replete-Subprecategory C subprecategory-Replete-Subprecategory
  is-replete-Replete-Subprecategory = pr2 P
```

## Properties

### Subprecategories of categories are replete

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-category-C : is-category-Precategory C)
  where

  based-is-in-iso-is-category-Subprecategory :
    {x : obj-Subprecategory C P}
    {y : obj-Precategory C}
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    is-in-iso-Subprecategory C P f
  based-is-in-iso-is-category-Subprecategory {x} f =
    ind-iso-Category
      ( C , is-category-C)
      ( λ B e → is-in-iso-Subprecategory C P e)
      ( is-in-iso-id-Subprecategory C P x)
      ( f)

  is-replete-is-category-Subprecategory : is-replete-Subprecategory C P
  is-replete-is-category-Subprecategory x y f =
    ind-iso-Category
      ( C , is-category-C)
      ( λ z e →
        Σ ( is-in-obj-Subprecategory C P z)
          ( λ z₀ →
            is-in-iso-obj-subprecategory-Subprecategory C P {x} {z , z₀} e))
      ( pr2 (is-in-iso-id-Subprecategory C P x))
      ( f)
```

### If a full subprecategory is closed under isomorphic objects then it is replete

This remains to be formalized.

## See also

- Every [subcategory](category-theory.subcategories.md) is replete.

## External links

- [replete subcategory](https://ncatlab.org/nlab/show/replete+replete-subprecategory)
  at nlab
- [Isomorphism-closed subcategory](https://en.wikipedia.org/wiki/Isomorphism-closed_subcategory)
  at Wikipedia
- [isomorphism-closed subcategory](https://www.wikidata.org/wiki/Q6086096) at
  Wikidata
