# Dependent products of precategories

```agda
module category-theory.dependent-products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [precategories](category-theory.precategories.md) `Pᵢ` indexed
by `i : I`, the dependent product `Π(i : I), Pᵢ` is a precategory consisting of
dependent functions taking `i : I` to an element of the underlying type of `Pᵢ`.
Every component of the structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (P : I → Precategory l2 l3)
  where

  obj-Π-Precategory : UU (l1 ⊔ l2)
  obj-Π-Precategory = (i : I) → obj-Precategory (P i)

  hom-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → Set (l1 ⊔ l3)
  hom-Π-Precategory x y = Π-Set' I (λ i → hom-Precategory (P i) (x i) (y i))

  type-hom-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → UU (l1 ⊔ l3)
  type-hom-Π-Precategory x y = type-Set (hom-Π-Precategory x y)

  comp-hom-Π-Precategory :
    {x y z : obj-Π-Precategory} →
    type-hom-Π-Precategory y z →
    type-hom-Π-Precategory x y →
    type-hom-Π-Precategory x z
  comp-hom-Π-Precategory f g i = comp-hom-Precategory (P i) (f i) (g i)

  associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : type-hom-Π-Precategory z w)
    (g : type-hom-Π-Precategory y z)
    (f : type-hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f) ＝
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f))
  associative-comp-hom-Π-Precategory h g f =
    eq-htpy (λ i → associative-comp-hom-Precategory (P i) (h i) (g i) (f i))

  associative-composition-Π-Precategory :
    associative-composition-structure-Set hom-Π-Precategory
  pr1 associative-composition-Π-Precategory = comp-hom-Π-Precategory
  pr2 associative-composition-Π-Precategory = associative-comp-hom-Π-Precategory

  id-hom-Π-Precategory : {x : obj-Π-Precategory} → type-hom-Π-Precategory x x
  id-hom-Π-Precategory i = id-hom-Precategory (P i)

  left-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory}
    (f : type-hom-Π-Precategory x y) →
    comp-hom-Π-Precategory id-hom-Π-Precategory f ＝ f
  left-unit-law-comp-hom-Π-Precategory f =
    eq-htpy (λ i → left-unit-law-comp-hom-Precategory (P i) (f i))

  right-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory} (f : type-hom-Π-Precategory x y) →
    comp-hom-Π-Precategory f id-hom-Π-Precategory ＝ f
  right-unit-law-comp-hom-Π-Precategory f =
    eq-htpy (λ i → right-unit-law-comp-hom-Precategory (P i) (f i))

  is-unital-Π-Precategory :
    is-unital-composition-structure-Set
      hom-Π-Precategory
      associative-composition-Π-Precategory
  pr1 is-unital-Π-Precategory x = id-hom-Π-Precategory
  pr1 (pr2 is-unital-Π-Precategory) = left-unit-law-comp-hom-Π-Precategory
  pr2 (pr2 is-unital-Π-Precategory) = right-unit-law-comp-hom-Π-Precategory

  Π-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 Π-Precategory = obj-Π-Precategory
  pr1 (pr2 Π-Precategory) = hom-Π-Precategory
  pr1 (pr2 (pr2 Π-Precategory)) = associative-composition-Π-Precategory
  pr2 (pr2 (pr2 Π-Precategory)) = is-unital-Π-Precategory
```
