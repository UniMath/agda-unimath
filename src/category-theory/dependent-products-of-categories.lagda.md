# Dependent products of categories

```agda
module category-theory.dependent-products-of-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.dependent-products-of-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [categories](category-theory.categories.md) `Cᵢ` indexed by
`i : I`, the dependent product type `Π(i : I), Cᵢ` is a category consisting of
functions taking `i : I` to an object of `Cᵢ`. Every component of the structure
is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Category l2 l3)
  where

  precategory-Π-Category : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  precategory-Π-Category = Π-Precategory I (precategory-Category ∘ C)

  abstract
    is-category-Π-Category :
      is-category-Precategory precategory-Π-Category
    is-category-Π-Category x y =
      is-equiv-htpy-equiv
        ( equiv-iso-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C) ∘e
          equiv-Π-equiv-family
            ( λ i → extensionality-obj-Category (C i) (x i) (y i)) ∘e
          equiv-funext)
        ( λ where refl → refl)

  Π-Category : Category (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 Π-Category = Π-Precategory I (precategory-Category ∘ C)
  pr2 Π-Category = is-category-Π-Category

  obj-Π-Category : UU (l1 ⊔ l2)
  obj-Π-Category = obj-Category Π-Category

  hom-set-Π-Category :
    obj-Π-Category → obj-Π-Category → Set (l1 ⊔ l3)
  hom-set-Π-Category = hom-set-Category Π-Category

  hom-Π-Category :
    obj-Π-Category → obj-Π-Category → UU (l1 ⊔ l3)
  hom-Π-Category = hom-Category Π-Category

  comp-hom-Π-Category :
    {x y z : obj-Π-Category} →
    hom-Π-Category y z →
    hom-Π-Category x y →
    hom-Π-Category x z
  comp-hom-Π-Category = comp-hom-Category Π-Category

  involutive-eq-associative-comp-hom-Π-Category :
    {x y z w : obj-Π-Category}
    (h : hom-Π-Category z w)
    (g : hom-Π-Category y z)
    (f : hom-Π-Category x y) →
    comp-hom-Π-Category (comp-hom-Π-Category h g) f ＝ⁱ
    comp-hom-Π-Category h (comp-hom-Π-Category g f)
  involutive-eq-associative-comp-hom-Π-Category =
    involutive-eq-associative-comp-hom-Category Π-Category

  associative-comp-hom-Π-Category :
    {x y z w : obj-Π-Category}
    (h : hom-Π-Category z w)
    (g : hom-Π-Category y z)
    (f : hom-Π-Category x y) →
    comp-hom-Π-Category (comp-hom-Π-Category h g) f ＝
    comp-hom-Π-Category h (comp-hom-Π-Category g f)
  associative-comp-hom-Π-Category =
    associative-comp-hom-Category Π-Category

  associative-composition-operation-Π-Category :
    associative-composition-operation-binary-family-Set hom-set-Π-Category
  associative-composition-operation-Π-Category =
    associative-composition-operation-Category Π-Category

  id-hom-Π-Category :
    {x : obj-Π-Category} → hom-Π-Category x x
  id-hom-Π-Category = id-hom-Category Π-Category

  left-unit-law-comp-hom-Π-Category :
    {x y : obj-Π-Category}
    (f : hom-Π-Category x y) →
    comp-hom-Π-Category id-hom-Π-Category f ＝ f
  left-unit-law-comp-hom-Π-Category =
    left-unit-law-comp-hom-Category Π-Category

  right-unit-law-comp-hom-Π-Category :
    {x y : obj-Π-Category} (f : hom-Π-Category x y) →
    comp-hom-Π-Category f id-hom-Π-Category ＝ f
  right-unit-law-comp-hom-Π-Category =
    right-unit-law-comp-hom-Category Π-Category

  is-unital-Π-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Π-Category
      comp-hom-Π-Category
  is-unital-Π-Category = is-unital-composition-operation-Category Π-Category

  extensionality-obj-Π-Category :
    (x y : obj-Category Π-Category) → (x ＝ y) ≃ iso-Category Π-Category x y
  extensionality-obj-Π-Category = extensionality-obj-Category Π-Category
```

## Properties

### Isomorphisms in the dependent product category are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Category l2 l3)
  {x y : obj-Π-Category I C}
  where

  is-fiberwise-iso-is-iso-Π-Category :
    (f : hom-Π-Category I C x y) →
    is-iso-Category (Π-Category I C) f →
    (i : I) → is-iso-Category (C i) (f i)
  is-fiberwise-iso-is-iso-Π-Category =
    is-fiberwise-iso-is-iso-Π-Precategory I (precategory-Category ∘ C)

  fiberwise-iso-iso-Π-Category :
    iso-Category (Π-Category I C) x y →
    (i : I) → iso-Category (C i) (x i) (y i)
  fiberwise-iso-iso-Π-Category =
    fiberwise-iso-iso-Π-Precategory I (precategory-Category ∘ C)

  is-iso-is-fiberwise-iso-Π-Category :
    (f : hom-Π-Category I C x y) →
    ((i : I) → is-iso-Category (C i) (f i)) →
    is-iso-Category (Π-Category I C) f
  is-iso-is-fiberwise-iso-Π-Category =
    is-iso-is-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)

  iso-fiberwise-iso-Π-Category :
    ((i : I) → iso-Category (C i) (x i) (y i)) →
    iso-Category (Π-Category I C) x y
  iso-fiberwise-iso-Π-Category =
    iso-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)

  is-equiv-is-fiberwise-iso-is-iso-Π-Category :
    (f : hom-Π-Category I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Category f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Category =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategory I (precategory-Category ∘ C)

  equiv-is-fiberwise-iso-is-iso-Π-Category :
    (f : hom-Π-Category I C x y) →
    ( is-iso-Category (Π-Category I C) f) ≃
    ( (i : I) → is-iso-Category (C i) (f i))
  equiv-is-fiberwise-iso-is-iso-Π-Category =
    equiv-is-fiberwise-iso-is-iso-Π-Precategory I (precategory-Category ∘ C)

  is-equiv-is-iso-is-fiberwise-iso-Π-Category :
    (f : hom-Π-Category I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Category f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Category =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)

  equiv-is-iso-is-fiberwise-iso-Π-Category :
    ( f : hom-Π-Category I C x y) →
    ( (i : I) → is-iso-Category (C i) (f i)) ≃
    ( is-iso-Category (Π-Category I C) f)
  equiv-is-iso-is-fiberwise-iso-Π-Category =
    equiv-is-iso-is-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)

  is-equiv-fiberwise-iso-iso-Π-Category :
    is-equiv fiberwise-iso-iso-Π-Category
  is-equiv-fiberwise-iso-iso-Π-Category =
    is-equiv-fiberwise-iso-iso-Π-Precategory I (precategory-Category ∘ C)

  equiv-fiberwise-iso-iso-Π-Category :
    ( iso-Category (Π-Category I C) x y) ≃
    ( (i : I) → iso-Category (C i) (x i) (y i))
  equiv-fiberwise-iso-iso-Π-Category =
    equiv-fiberwise-iso-iso-Π-Precategory I (precategory-Category ∘ C)

  is-equiv-iso-fiberwise-iso-Π-Category :
    is-equiv iso-fiberwise-iso-Π-Category
  is-equiv-iso-fiberwise-iso-Π-Category =
    is-equiv-iso-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)

  equiv-iso-fiberwise-iso-Π-Category :
    ( (i : I) → iso-Category (C i) (x i) (y i)) ≃
    ( iso-Category (Π-Category I C) x y)
  equiv-iso-fiberwise-iso-Π-Category =
    equiv-iso-fiberwise-iso-Π-Precategory I (precategory-Category ∘ C)
```
