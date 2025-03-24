# Dependent products of large categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.dependent-products-of-large-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-precategories funext univalence truncations
open import category-theory.isomorphisms-in-large-categories funext univalence truncations
open import category-theory.large-categories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations

open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.strictly-involutive-identity-types funext univalence
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [large categories](category-theory.large-categories.md) `Cᵢ`
indexed by `i : I`, the dependent product `Π(i : I), Cᵢ` is a large category
consisting of functions taking `i : I` to an object of `Cᵢ`. Every component of
the structure is given pointwise.

## Definition

```agda
module _
  {l1 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : I → Large-Category α β)
  where

  large-precategory-Π-Large-Category :
    Large-Precategory (λ l2 → l1 ⊔ α l2) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-precategory-Π-Large-Category =
    Π-Large-Precategory I (λ i → large-precategory-Large-Category (C i))

  abstract
    is-large-category-Π-Large-Category :
      is-large-category-Large-Precategory large-precategory-Π-Large-Category
    is-large-category-Π-Large-Category x y =
      is-equiv-htpy-equiv
        ( ( equiv-iso-fiberwise-iso-Π-Large-Precategory I
            ( λ i → large-precategory-Large-Category (C i))) ∘e
          ( equiv-Π-equiv-family
            ( λ i → extensionality-obj-Large-Category (C i) (x i) (y i))) ∘e
          ( equiv-funext))
        ( λ where refl → refl)

  Π-Large-Category : Large-Category (λ l2 → l1 ⊔ α l2) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-precategory-Large-Category
    Π-Large-Category =
    large-precategory-Π-Large-Category
  is-large-category-Large-Category Π-Large-Category =
    is-large-category-Π-Large-Category

  obj-Π-Large-Category : (l2 : Level) → UU (l1 ⊔ α l2)
  obj-Π-Large-Category = obj-Large-Category Π-Large-Category

  hom-set-Π-Large-Category :
    {l2 l3 : Level} →
    obj-Π-Large-Category l2 → obj-Π-Large-Category l3 → Set (l1 ⊔ β l2 l3)
  hom-set-Π-Large-Category = hom-set-Large-Category Π-Large-Category

  hom-Π-Large-Category :
    {l2 l3 : Level} →
    obj-Π-Large-Category l2 → obj-Π-Large-Category l3 → UU (l1 ⊔ β l2 l3)
  hom-Π-Large-Category = hom-Large-Category Π-Large-Category

  comp-hom-Π-Large-Category :
    {l2 l3 l4 : Level}
    {x : obj-Π-Large-Category l2}
    {y : obj-Π-Large-Category l3}
    {z : obj-Π-Large-Category l4} →
    hom-Π-Large-Category y z →
    hom-Π-Large-Category x y →
    hom-Π-Large-Category x z
  comp-hom-Π-Large-Category = comp-hom-Large-Category Π-Large-Category

  associative-comp-hom-Π-Large-Category :
    {l2 l3 l4 l5 : Level}
    {x : obj-Π-Large-Category l2}
    {y : obj-Π-Large-Category l3}
    {z : obj-Π-Large-Category l4}
    {w : obj-Π-Large-Category l5} →
    (h : hom-Π-Large-Category z w)
    (g : hom-Π-Large-Category y z)
    (f : hom-Π-Large-Category x y) →
    comp-hom-Π-Large-Category (comp-hom-Π-Large-Category h g) f ＝
    comp-hom-Π-Large-Category h (comp-hom-Π-Large-Category g f)
  associative-comp-hom-Π-Large-Category =
    associative-comp-hom-Large-Category Π-Large-Category

  involutive-eq-associative-comp-hom-Π-Large-Category :
    {l2 l3 l4 l5 : Level}
    {x : obj-Π-Large-Category l2}
    {y : obj-Π-Large-Category l3}
    {z : obj-Π-Large-Category l4}
    {w : obj-Π-Large-Category l5} →
    (h : hom-Π-Large-Category z w)
    (g : hom-Π-Large-Category y z)
    (f : hom-Π-Large-Category x y) →
    comp-hom-Π-Large-Category (comp-hom-Π-Large-Category h g) f ＝ⁱ
    comp-hom-Π-Large-Category h (comp-hom-Π-Large-Category g f)
  involutive-eq-associative-comp-hom-Π-Large-Category =
    involutive-eq-associative-comp-hom-Large-Category Π-Large-Category

  id-hom-Π-Large-Category :
    {l2 : Level} {x : obj-Π-Large-Category l2} →
    hom-Π-Large-Category x x
  id-hom-Π-Large-Category = id-hom-Large-Category Π-Large-Category

  left-unit-law-comp-hom-Π-Large-Category :
    {l2 l3 : Level} {x : obj-Π-Large-Category l2} {y : obj-Π-Large-Category l3}
    (f : hom-Π-Large-Category x y) →
    comp-hom-Π-Large-Category id-hom-Π-Large-Category f ＝ f
  left-unit-law-comp-hom-Π-Large-Category =
    left-unit-law-comp-hom-Large-Category Π-Large-Category

  right-unit-law-comp-hom-Π-Large-Category :
    {l2 l3 : Level} {x : obj-Π-Large-Category l2} {y : obj-Π-Large-Category l3}
    (f : hom-Π-Large-Category x y) →
    comp-hom-Π-Large-Category f id-hom-Π-Large-Category ＝ f
  right-unit-law-comp-hom-Π-Large-Category =
    right-unit-law-comp-hom-Large-Category Π-Large-Category

  extensionality-obj-Π-Large-Category :
    {l2 : Level} (x y : obj-Π-Large-Category l2) →
    (x ＝ y) ≃ iso-Large-Category Π-Large-Category x y
  extensionality-obj-Π-Large-Category =
    extensionality-obj-Large-Category Π-Large-Category
```

## Properties

### Isomorphisms in the large dependent product category are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : I → Large-Category α β)
  {x : obj-Π-Large-Category I C l2} {y : obj-Π-Large-Category I C l3}
  where

  is-fiberwise-iso-is-iso-Π-Large-Category :
    (f : hom-Π-Large-Category I C x y) →
    is-iso-Large-Category (Π-Large-Category I C) f →
    (i : I) → is-iso-Large-Category (C i) (f i)
  is-fiberwise-iso-is-iso-Π-Large-Category =
    is-fiberwise-iso-is-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  fiberwise-iso-iso-Π-Large-Category :
    iso-Large-Category (Π-Large-Category I C) x y →
    (i : I) → iso-Large-Category (C i) (x i) (y i)
  fiberwise-iso-iso-Π-Large-Category =
    fiberwise-iso-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  is-iso-is-fiberwise-iso-Π-Large-Category :
    (f : hom-Π-Large-Category I C x y) →
    ((i : I) → is-iso-Large-Category (C i) (f i)) →
    is-iso-Large-Category (Π-Large-Category I C) f
  is-iso-is-fiberwise-iso-Π-Large-Category =
    is-iso-is-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  iso-fiberwise-iso-Π-Large-Category :
    ((i : I) → iso-Large-Category (C i) (x i) (y i)) →
    iso-Large-Category (Π-Large-Category I C) x y
  iso-fiberwise-iso-Π-Large-Category =
    iso-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Category :
    (f : hom-Π-Large-Category I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Large-Category f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Category =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  equiv-is-fiberwise-iso-is-iso-Π-Large-Category :
    (f : hom-Π-Large-Category I C x y) →
    ( is-iso-Large-Category (Π-Large-Category I C) f) ≃
    ( (i : I) → is-iso-Large-Category (C i) (f i))
  equiv-is-fiberwise-iso-is-iso-Π-Large-Category =
    equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Category :
    (f : hom-Π-Large-Category I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Large-Category f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Category =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  equiv-is-iso-is-fiberwise-iso-Π-Large-Category :
    ( f : hom-Π-Large-Category I C x y) →
    ( (i : I) → is-iso-Large-Category (C i) (f i)) ≃
    ( is-iso-Large-Category (Π-Large-Category I C) f)
  equiv-is-iso-is-fiberwise-iso-Π-Large-Category =
    equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  is-equiv-fiberwise-iso-iso-Π-Large-Category :
    is-equiv fiberwise-iso-iso-Π-Large-Category
  is-equiv-fiberwise-iso-iso-Π-Large-Category =
    is-equiv-fiberwise-iso-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  equiv-fiberwise-iso-iso-Π-Large-Category :
    ( iso-Large-Category (Π-Large-Category I C) x y) ≃
    ( (i : I) → iso-Large-Category (C i) (x i) (y i))
  equiv-fiberwise-iso-iso-Π-Large-Category =
    equiv-fiberwise-iso-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  is-equiv-iso-fiberwise-iso-Π-Large-Category :
    is-equiv iso-fiberwise-iso-Π-Large-Category
  is-equiv-iso-fiberwise-iso-Π-Large-Category =
    is-equiv-iso-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))

  equiv-iso-fiberwise-iso-Π-Large-Category :
    ( (i : I) → iso-Large-Category (C i) (x i) (y i)) ≃
    ( iso-Large-Category (Π-Large-Category I C) x y)
  equiv-iso-fiberwise-iso-Π-Large-Category =
    equiv-iso-fiberwise-iso-Π-Large-Precategory I
      ( λ i → large-precategory-Large-Category (C i))
```
