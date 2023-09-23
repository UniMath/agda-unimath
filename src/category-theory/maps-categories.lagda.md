# Maps between categories

```agda
module category-theory.maps-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-categories
open import category-theory.categories
open import category-theory.maps-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-binary-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [precategory](category-theory.categories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definition

### Maps between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  map-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Category =
    map-Precategory (precategory-Category C) (precategory-Category D)

  obj-map-Category :
    (F : map-Category) → obj-Category C → obj-Category D
  obj-map-Category =
    obj-map-Precategory (precategory-Category C) (precategory-Category D)

  hom-map-Category :
    (F : map-Category)
    {x y : obj-Category C} →
    hom-Category C x y →
    hom-Category D
      ( obj-map-Category F x)
      ( obj-map-Category F y)
  hom-map-Category =
    hom-map-Precategory (precategory-Category C) (precategory-Category D)
```

## Properties

### Characterization of equality of maps between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  coherence-htpy-map-Category :
    (f g : map-Category C D) →
    (obj-map-Category C D f ~ obj-map-Category C D g) →
    UU (l1 ⊔ l2 ⊔ l4)
  coherence-htpy-map-Category =
    coherence-htpy-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  htpy-map-Category :
    (f g : map-Category C D) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-map-Category =
    htpy-map-Precategory (precategory-Category C) (precategory-Category D)

  refl-htpy-map-Category :
    (f : map-Category C D) → htpy-map-Category f f
  refl-htpy-map-Category =
    refl-htpy-map-Precategory (precategory-Category C) (precategory-Category D)

  htpy-eq-map-Category :
    (f g : map-Category C D) → (f ＝ g) → htpy-map-Category f g
  htpy-eq-map-Category =
    htpy-eq-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  is-contr-total-htpy-map-Category :
    (f : map-Category C D) →
    is-contr (Σ (map-Category C D) (htpy-map-Category f))
  is-contr-total-htpy-map-Category =
    is-contr-total-htpy-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  is-equiv-htpy-eq-map-Category :
    (f g : map-Category C D) → is-equiv (htpy-eq-map-Category f g)
  is-equiv-htpy-eq-map-Category =
    is-equiv-htpy-eq-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  extensionality-map-Category :
    (f g : map-Category C D) → (f ＝ g) ≃ htpy-map-Category f g
  extensionality-map-Category =
    extensionality-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  eq-htpy-map-Category :
    (f g : map-Category C D) → htpy-map-Category f g → (f ＝ g)
  eq-htpy-map-Category =
    eq-htpy-map-Precategory (precategory-Category C) (precategory-Category D)
```

## See also

- [Functors between categories](category-theory.functors-categories.md)
