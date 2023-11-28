# Dependent products of precategories

```agda
module category-theory.dependent-products-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [precategories](category-theory.precategories.md) `Pᵢ` indexed
by `i : I`, the dependent product `Π(i : I), Pᵢ` is a precategory consisting of
dependent functions taking `i : I` to an object of `Pᵢ`. Every component of the
structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Precategory l2 l3)
  where

  obj-Π-Precategory : UU (l1 ⊔ l2)
  obj-Π-Precategory = (i : I) → obj-Precategory (C i)

  hom-set-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → Set (l1 ⊔ l3)
  hom-set-Π-Precategory x y =
    Π-Set' I (λ i → hom-set-Precategory (C i) (x i) (y i))

  hom-Π-Precategory : obj-Π-Precategory → obj-Π-Precategory → UU (l1 ⊔ l3)
  hom-Π-Precategory x y = type-Set (hom-set-Π-Precategory x y)

  comp-hom-Π-Precategory :
    {x y z : obj-Π-Precategory} →
    hom-Π-Precategory y z →
    hom-Π-Precategory x y →
    hom-Π-Precategory x z
  comp-hom-Π-Precategory f g i = comp-hom-Precategory (C i) (f i) (g i)

  associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f) ＝
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f))
  associative-comp-hom-Π-Precategory h g f =
    eq-htpy (λ i → associative-comp-hom-Precategory (C i) (h i) (g i) (f i))

  inv-associative-comp-hom-Π-Precategory :
    {x y z w : obj-Π-Precategory}
    (h : hom-Π-Precategory z w)
    (g : hom-Π-Precategory y z)
    (f : hom-Π-Precategory x y) →
    ( comp-hom-Π-Precategory h (comp-hom-Π-Precategory g f)) ＝
    ( comp-hom-Π-Precategory (comp-hom-Π-Precategory h g) f)
  inv-associative-comp-hom-Π-Precategory h g f =
    eq-htpy (λ i → inv-associative-comp-hom-Precategory (C i) (h i) (g i) (f i))

  associative-composition-operation-Π-Precategory :
    associative-composition-operation-binary-family-Set hom-set-Π-Precategory
  pr1 associative-composition-operation-Π-Precategory = comp-hom-Π-Precategory
  pr1 (pr2 associative-composition-operation-Π-Precategory h g f) =
    associative-comp-hom-Π-Precategory h g f
  pr2 (pr2 associative-composition-operation-Π-Precategory h g f) =
    inv-associative-comp-hom-Π-Precategory h g f

  id-hom-Π-Precategory : {x : obj-Π-Precategory} → hom-Π-Precategory x x
  id-hom-Π-Precategory i = id-hom-Precategory (C i)

  left-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory}
    (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory id-hom-Π-Precategory f ＝ f
  left-unit-law-comp-hom-Π-Precategory f =
    eq-htpy (λ i → left-unit-law-comp-hom-Precategory (C i) (f i))

  right-unit-law-comp-hom-Π-Precategory :
    {x y : obj-Π-Precategory} (f : hom-Π-Precategory x y) →
    comp-hom-Π-Precategory f id-hom-Π-Precategory ＝ f
  right-unit-law-comp-hom-Π-Precategory f =
    eq-htpy (λ i → right-unit-law-comp-hom-Precategory (C i) (f i))

  is-unital-Π-Precategory :
    is-unital-composition-operation-binary-family-Set
      hom-set-Π-Precategory
      comp-hom-Π-Precategory
  pr1 is-unital-Π-Precategory x = id-hom-Π-Precategory
  pr1 (pr2 is-unital-Π-Precategory) = left-unit-law-comp-hom-Π-Precategory
  pr2 (pr2 is-unital-Π-Precategory) = right-unit-law-comp-hom-Π-Precategory

  Π-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 Π-Precategory = obj-Π-Precategory
  pr1 (pr2 Π-Precategory) = hom-set-Π-Precategory
  pr1 (pr2 (pr2 Π-Precategory)) =
    associative-composition-operation-Π-Precategory
  pr2 (pr2 (pr2 Π-Precategory)) = is-unital-Π-Precategory
```

## Properties

### Isomorphisms in the dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Precategory l2 l3)
  {x y : obj-Π-Precategory I C}
  where

  is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-iso-Precategory (Π-Precategory I C) f →
    (i : I) → is-iso-Precategory (C i) (f i)
  pr1 (is-fiberwise-iso-is-iso-Π-Precategory f is-iso-f i) =
    hom-inv-is-iso-Precategory (Π-Precategory I C) is-iso-f i
  pr1 (pr2 (is-fiberwise-iso-is-iso-Π-Precategory f is-iso-f i)) =
    htpy-eq
      ( is-section-hom-inv-is-iso-Precategory (Π-Precategory I C) is-iso-f)
      ( i)
  pr2 (pr2 (is-fiberwise-iso-is-iso-Π-Precategory f is-iso-f i)) =
    htpy-eq
      ( is-retraction-hom-inv-is-iso-Precategory
        ( Π-Precategory I C)
        ( is-iso-f))
      ( i)

  fiberwise-iso-iso-Π-Precategory :
    iso-Precategory (Π-Precategory I C) x y →
    (i : I) → iso-Precategory (C i) (x i) (y i)
  pr1 (fiberwise-iso-iso-Π-Precategory e i) =
    hom-iso-Precategory (Π-Precategory I C) e i
  pr2 (fiberwise-iso-iso-Π-Precategory e i) =
    is-fiberwise-iso-is-iso-Π-Precategory
      ( hom-iso-Precategory (Π-Precategory I C) e)
      ( is-iso-iso-Precategory (Π-Precategory I C) e)
      ( i)

  is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ((i : I) → is-iso-Precategory (C i) (f i)) →
    is-iso-Precategory (Π-Precategory I C) f
  pr1 (is-iso-is-fiberwise-iso-Π-Precategory f is-fiberwise-iso-f) i =
    hom-inv-is-iso-Precategory (C i) (is-fiberwise-iso-f i)
  pr1 (pr2 (is-iso-is-fiberwise-iso-Π-Precategory f is-fiberwise-iso-f)) =
    eq-htpy
      ( λ i →
        is-section-hom-inv-is-iso-Precategory (C i) (is-fiberwise-iso-f i))
  pr2 (pr2 (is-iso-is-fiberwise-iso-Π-Precategory f is-fiberwise-iso-f)) =
    eq-htpy
      ( λ i →
        is-retraction-hom-inv-is-iso-Precategory
          ( C i)
          ( is-fiberwise-iso-f i))

  iso-fiberwise-iso-Π-Precategory :
    ((i : I) → iso-Precategory (C i) (x i) (y i)) →
    iso-Precategory (Π-Precategory I C) x y
  pr1 (iso-fiberwise-iso-Π-Precategory e) i = hom-iso-Precategory (C i) (e i)
  pr2 (iso-fiberwise-iso-Π-Precategory e) =
    is-iso-is-fiberwise-iso-Π-Precategory
      ( λ i → hom-iso-Precategory (C i) (e i))
      ( λ i → is-iso-iso-Precategory (C i) (e i))

  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Π-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-Π-Precategory f =
    is-equiv-is-prop
      ( is-prop-is-iso-Precategory (Π-Precategory I C) f)
      ( is-prop-Π (λ i → is-prop-is-iso-Precategory (C i) (f i)))
      ( is-iso-is-fiberwise-iso-Π-Precategory f)

  equiv-is-fiberwise-iso-is-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    ( is-iso-Precategory (Π-Precategory I C) f) ≃
    ( (i : I) → is-iso-Precategory (C i) (f i))
  pr1 (equiv-is-fiberwise-iso-is-iso-Π-Precategory f) =
    is-fiberwise-iso-is-iso-Π-Precategory f
  pr2 (equiv-is-fiberwise-iso-is-iso-Π-Precategory f) =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategory f

  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    (f : hom-Π-Precategory I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Π-Precategory f)
  is-equiv-is-iso-is-fiberwise-iso-Π-Precategory f =
    is-equiv-is-prop
      ( is-prop-Π (λ i → is-prop-is-iso-Precategory (C i) (f i)))
      ( is-prop-is-iso-Precategory (Π-Precategory I C) f)
      ( is-fiberwise-iso-is-iso-Π-Precategory f)

  equiv-is-iso-is-fiberwise-iso-Π-Precategory :
    ( f : hom-Π-Precategory I C x y) →
    ( (i : I) → is-iso-Precategory (C i) (f i)) ≃
    ( is-iso-Precategory (Π-Precategory I C) f)
  pr1 (equiv-is-iso-is-fiberwise-iso-Π-Precategory f) =
    is-iso-is-fiberwise-iso-Π-Precategory f
  pr2 (equiv-is-iso-is-fiberwise-iso-Π-Precategory f) =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategory f

  is-equiv-fiberwise-iso-iso-Π-Precategory :
    is-equiv fiberwise-iso-iso-Π-Precategory
  is-equiv-fiberwise-iso-iso-Π-Precategory =
    is-equiv-is-invertible
      ( iso-fiberwise-iso-Π-Precategory)
      ( λ e →
        eq-htpy
          ( λ i → eq-type-subtype (is-iso-prop-Precategory (C i)) refl))
      ( λ e →
        eq-type-subtype (is-iso-prop-Precategory (Π-Precategory I C)) refl)

  equiv-fiberwise-iso-iso-Π-Precategory :
    ( iso-Precategory (Π-Precategory I C) x y) ≃
    ( (i : I) → iso-Precategory (C i) (x i) (y i))
  pr1 equiv-fiberwise-iso-iso-Π-Precategory =
    fiberwise-iso-iso-Π-Precategory
  pr2 equiv-fiberwise-iso-iso-Π-Precategory =
    is-equiv-fiberwise-iso-iso-Π-Precategory

  is-equiv-iso-fiberwise-iso-Π-Precategory :
    is-equiv iso-fiberwise-iso-Π-Precategory
  is-equiv-iso-fiberwise-iso-Π-Precategory =
    is-equiv-map-inv-is-equiv is-equiv-fiberwise-iso-iso-Π-Precategory

  equiv-iso-fiberwise-iso-Π-Precategory :
    ( (i : I) → iso-Precategory (C i) (x i) (y i)) ≃
    ( iso-Precategory (Π-Precategory I C) x y)
  pr1 equiv-iso-fiberwise-iso-Π-Precategory =
    iso-fiberwise-iso-Π-Precategory
  pr2 equiv-iso-fiberwise-iso-Π-Precategory =
    is-equiv-iso-fiberwise-iso-Π-Precategory
```
