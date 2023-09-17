# Isomorphisms in categories

```agda
module category-theory.isomorphisms-in-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism in a category is an isomorphism in the underlying precategory.

## Definition

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-iso-Category :
    {x y : obj-Category C} (f : type-hom-Category C x y) → UU l2
  is-iso-Category = is-iso-Precategory (precategory-Category C)

  hom-inv-is-iso-Category :
    {x y : obj-Category C} {f : type-hom-Category C x y} →
    is-iso-Category f → type-hom-Category C y x
  hom-inv-is-iso-Category = hom-inv-is-iso-Precategory (precategory-Category C)

  is-section-hom-inv-is-iso-Category :
    {x y : obj-Category C} {f : type-hom-Category C x y}
    (H : is-iso-Category f) →
    comp-hom-Category C f (hom-inv-is-iso-Category H) ＝
    id-hom-Category C
  is-section-hom-inv-is-iso-Category =
    is-section-hom-inv-is-iso-Precategory (precategory-Category C)

  is-retraction-hom-inv-is-iso-Category :
    {x y : obj-Category C} {f : type-hom-Category C x y}
    (H : is-iso-Category f) →
    comp-hom-Category C (hom-inv-is-iso-Category H) f ＝
    id-hom-Category C
  is-retraction-hom-inv-is-iso-Category =
    is-retraction-hom-inv-is-iso-Precategory (precategory-Category C)

  is-prop-is-iso-Category :
    {x y : obj-Category C} (f : type-hom-Category C x y) →
    is-prop (is-iso-Category f)
  is-prop-is-iso-Category = is-prop-is-iso-Precategory (precategory-Category C)

  is-iso-Category-Prop :
    {x y : obj-Category C} (f : type-hom-Category C x y) → Prop l2
  is-iso-Category-Prop = is-iso-Precategory-Prop (precategory-Category C)
```

### The type of isomorphisms between two objects

```agda
  iso-Category : (x y : obj-Category C) → UU l2
  iso-Category = iso-Precategory (precategory-Category C)

  hom-iso-Category :
    {x y : obj-Category C} → iso-Category x y → type-hom-Category C x y
  hom-iso-Category = hom-iso-Precategory (precategory-Category C)

  is-iso-hom-iso-Category :
    {x y : obj-Category C} (f : iso-Category x y) →
    is-iso-Category (hom-iso-Category f)
  is-iso-hom-iso-Category = is-iso-hom-iso-Precategory (precategory-Category C)

  hom-inv-iso-Category :
    {x y : obj-Category C} → iso-Category x y → type-hom-Category C y x
  hom-inv-iso-Category = hom-inv-iso-Precategory (precategory-Category C)

  is-section-hom-inv-iso-Category :
    { x y : obj-Category C}
    ( f : iso-Category x y) →
    ( comp-hom-Category C
      ( hom-iso-Category f)
      ( hom-inv-iso-Category f)) ＝
    ( id-hom-Category C)
  is-section-hom-inv-iso-Category =
    is-section-hom-inv-iso-Precategory (precategory-Category C)

  is-retraction-hom-inv-iso-Category :
    { x y : obj-Category C}
    ( f : iso-Category x y) →
    ( comp-hom-Category C (hom-inv-iso-Category f) (hom-iso-Category f)) ＝
    ( id-hom-Category C)
  is-retraction-hom-inv-iso-Category =
    is-retraction-hom-inv-iso-Precategory (precategory-Category C)

  inv-iso-Category :
    {x y : obj-Category C} → iso-Category x y → iso-Category y x
  inv-iso-Category = inv-iso-Precategory (precategory-Category C)
```

### Precomposing by isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  precomp-iso-Category :
    {x y z : obj-Category C} →
    iso-Category C x y → type-hom-Category C y z → type-hom-Category C x z
  precomp-iso-Category f g = comp-hom-Category C g (hom-iso-Category C f)
```

### Postcomposing by isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  postcomp-iso-Category :
    {x y z : obj-Category C} →
    iso-Category C y z → type-hom-Category C x y → type-hom-Category C x z
  postcomp-iso-Category f g = comp-hom-Category C (hom-iso-Category C f) g
```

## Examples

### The identity morphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-iso-id-hom-Category :
    {x : obj-Category C} → is-iso-Category C (id-hom-Category C {x})
  is-iso-id-hom-Category = is-iso-id-hom-Precategory (precategory-Category C)

  id-iso-Category : {x : obj-Category C} → iso-Category C x x
  id-iso-Category = id-iso-Precategory (precategory-Category C)
```

### Compositions of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  hom-comp-iso-Category :
    {x y z : obj-Category C} →
    iso-Category C y z → iso-Category C x y → type-hom-Category C x z
  hom-comp-iso-Category g f =
    comp-hom-Category C (hom-iso-Category C g) (hom-iso-Category C f)

  hom-inv-comp-iso-Category :
    {x y z : obj-Category C} →
    iso-Category C y z → iso-Category C x y → type-hom-Category C z x
  hom-inv-comp-iso-Category g f =
    comp-hom-Category C (hom-inv-iso-Category C f) (hom-inv-iso-Category C g)

  is-section-hom-inv-comp-iso-Category :
    { x y z : obj-Category C}
    ( g : iso-Category C y z)
    ( f : iso-Category C x y) →
    ( comp-hom-Category C
      ( hom-comp-iso-Category g f)
      ( hom-inv-comp-iso-Category g f)) ＝
    ( id-hom-Category C)
  is-section-hom-inv-comp-iso-Category g f =
    equational-reasoning
      comp-hom-Category C
        ( hom-comp-iso-Category g f)
        ( hom-inv-comp-iso-Category g f)
      ＝ comp-hom-Category C
          ( hom-iso-Category C g)
          ( comp-hom-Category C
            ( hom-iso-Category C f)
            ( hom-inv-comp-iso-Category g f))
        by
          associative-comp-hom-Category C
            ( hom-iso-Category C g)
            ( hom-iso-Category C f)
            ( hom-inv-comp-iso-Category g f)
      ＝ comp-hom-Category C
          ( hom-iso-Category C g)
          ( comp-hom-Category C
            ( comp-hom-Category C
              ( hom-iso-Category C f)
              ( hom-inv-iso-Category C f))
            ( hom-inv-iso-Category C g))
        by
          ap
            ( comp-hom-Category C (hom-iso-Category C g))
            ( inv
              ( associative-comp-hom-Category C
                ( hom-iso-Category C f)
                ( hom-inv-iso-Category C f)
                ( hom-inv-iso-Category C g)))
      ＝ comp-hom-Category C
          ( hom-iso-Category C g)
          ( comp-hom-Category C
            ( id-hom-Category C)
            ( hom-inv-iso-Category C g))
        by
          ap
            ( comp-hom-Category C (hom-iso-Category C g))
            ( ap
              ( λ h → comp-hom-Category C h (hom-inv-iso-Category C g))
              ( is-section-hom-inv-iso-Category C f))
      ＝ comp-hom-Category C (hom-iso-Category C g) (hom-inv-iso-Category C g)
        by
          ap
            ( comp-hom-Category C (hom-iso-Category C g))
            ( left-unit-law-comp-hom-Category C (hom-inv-iso-Category C g))
      ＝ id-hom-Category C
        by is-section-hom-inv-iso-Category C g

  is-retraction-hom-inv-comp-iso-Category :
    {x y z : obj-Category C} (g : iso-Category C y z) (f : iso-Category C x y) →
    ( comp-hom-Category
      ( C)
      ( hom-inv-comp-iso-Category g f)
      ( hom-comp-iso-Category g f)) ＝
    ( id-hom-Category C)
  is-retraction-hom-inv-comp-iso-Category g f =
    equational-reasoning
      comp-hom-Category C
        ( hom-inv-comp-iso-Category g f)
        ( hom-comp-iso-Category g f)
      ＝ comp-hom-Category C
          ( hom-inv-iso-Category C f)
          ( comp-hom-Category C
            ( hom-inv-iso-Category C g)
            ( hom-comp-iso-Category g f))
        by
          associative-comp-hom-Category C
            ( hom-inv-iso-Category C f)
            ( hom-inv-iso-Category C g)
            ( hom-comp-iso-Category g f)
      ＝ comp-hom-Category C
          ( hom-inv-iso-Category C f)
          ( comp-hom-Category C
            ( comp-hom-Category C
              ( hom-inv-iso-Category C g)
              ( hom-iso-Category C g))
            ( hom-iso-Category C f))
        by
          ap
            ( comp-hom-Category C (hom-inv-iso-Category C f))
            ( inv
              ( associative-comp-hom-Category C
                ( hom-inv-iso-Category C g)
                ( hom-iso-Category C g)
                ( hom-iso-Category C f)))
      ＝ comp-hom-Category C
          ( hom-inv-iso-Category C f)
          ( comp-hom-Category C
            ( id-hom-Category C)
            ( hom-iso-Category C f))
        by
          ap
            ( comp-hom-Category C (hom-inv-iso-Category C f))
            ( ap
              ( λ h → comp-hom-Category C h (hom-iso-Category C f))
              ( is-retraction-hom-inv-iso-Category C g))
      ＝ comp-hom-Category C (hom-inv-iso-Category C f) (hom-iso-Category C f)
        by
          ap
            ( comp-hom-Category C (hom-inv-iso-Category C f))
            ( left-unit-law-comp-hom-Category C (hom-iso-Category C f))
      ＝ id-hom-Category C
        by is-retraction-hom-inv-iso-Category C f

  is-iso-hom-comp-iso-Category :
    {x y z : obj-Category C} (g : iso-Category C y z) (f : iso-Category C x y) →
    is-iso-Category C (hom-comp-iso-Category g f)
  pr1 (is-iso-hom-comp-iso-Category g f) =
    hom-inv-comp-iso-Category g f
  pr1 (pr2 (is-iso-hom-comp-iso-Category g f)) =
    is-section-hom-inv-comp-iso-Category g f
  pr2 (pr2 (is-iso-hom-comp-iso-Category g f)) =
    is-retraction-hom-inv-comp-iso-Category g f

  comp-iso-Category :
    {x y z : obj-Category C} →
    iso-Category C y z → iso-Category C x y → iso-Category C x z
  pr1 (comp-iso-Category g f) = hom-comp-iso-Category g f
  pr2 (comp-iso-Category g f) = is-iso-hom-comp-iso-Category g f
```

## Properties

### Characterizing equality of isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  where

  Eq-iso-Category : iso-Category C x y → UU l2
  Eq-iso-Category g = hom-iso-Category C f ＝ hom-iso-Category C g

  refl-Eq-iso-Category : Eq-iso-Category f
  refl-Eq-iso-Category = refl

  is-contr-total-Eq-iso-Category :
    is-contr (Σ (iso-Category C x y) Eq-iso-Category)
  is-contr-total-Eq-iso-Category =
    is-contr-total-Eq-subtype
      ( is-contr-total-path (hom-iso-Category C f))
      ( is-prop-is-iso-Category C)
      ( hom-iso-Category C f)
      ( refl)
      ( is-iso-hom-iso-Category C f)

  Eq-eq-iso-Category :
    (g : iso-Category C x y) → (f ＝ g) → Eq-iso-Category g
  Eq-eq-iso-Category .f refl = refl-Eq-iso-Category

  is-equiv-Eq-eq-iso-Category :
    (g : iso-Category C x y) → is-equiv (Eq-eq-iso-Category g)
  is-equiv-Eq-eq-iso-Category =
    fundamental-theorem-id
      is-contr-total-Eq-iso-Category
      Eq-eq-iso-Category

  extensionality-iso-Category :
    (g : iso-Category C x y) → (f ＝ g) ≃ Eq-iso-Category g
  pr1 (extensionality-iso-Category g) = Eq-eq-iso-Category g
  pr2 (extensionality-iso-Category g) = is-equiv-Eq-eq-iso-Category g

  eq-Eq-iso-Category :
    (g : iso-Category C x y) → Eq-iso-Category g → (f ＝ g)
  eq-Eq-iso-Category g = map-inv-equiv (extensionality-iso-Category g)
```

### Groupoid laws for composition of isomorphisms in a category

#### Left unit law

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  left-unit-law-comp-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    comp-iso-Category C (id-iso-Category C) f ＝ f
  left-unit-law-comp-iso-Category f =
    eq-Eq-iso-Category C
      (comp-iso-Category C (id-iso-Category C) f)
      ( f)
      ( left-unit-law-comp-hom-Category C (hom-iso-Category C f))
```

#### Right unit law

```agda
  right-unit-law-comp-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    comp-iso-Category C f (id-iso-Category C) ＝ f
  right-unit-law-comp-iso-Category f =
    eq-Eq-iso-Category C
      ( comp-iso-Category C f (id-iso-Category C))
      ( f)
      ( right-unit-law-comp-hom-Category C (hom-iso-Category C f))
```

#### Associatitivity

```agda
  associative-comp-iso-Category :
    {x y z w : obj-Category C}
    (h : iso-Category C z w) (g : iso-Category C y z) (f : iso-Category C x y) →
    comp-iso-Category C (comp-iso-Category C h g) f ＝
    comp-iso-Category C h (comp-iso-Category C g f)
  associative-comp-iso-Category h g f =
    eq-Eq-iso-Category C
      ( comp-iso-Category C (comp-iso-Category C h g) f)
      ( comp-iso-Category C h (comp-iso-Category C g f))
      ( associative-comp-hom-Category C
        ( hom-iso-Category C h)
        ( hom-iso-Category C g)
        ( hom-iso-Category C f))
```

#### Left inverse law

```agda
  left-inverse-law-comp-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    comp-iso-Category C (inv-iso-Category C f) f ＝ id-iso-Category C
  left-inverse-law-comp-iso-Category f =
    eq-Eq-iso-Category C
      ( comp-iso-Category C (inv-iso-Category C f) f)
      ( id-iso-Category C)
      ( is-retraction-hom-inv-iso-Category C f)
```

#### Right inverse law

```agda
  right-inverse-law-comp-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    comp-iso-Category C f (inv-iso-Category C f) ＝ id-iso-Category C
  right-inverse-law-comp-iso-Category f =
    eq-Eq-iso-Category C
      ( comp-iso-Category C f (inv-iso-Category C f))
      ( id-iso-Category C)
      ( is-section-hom-inv-iso-Category C f)
```

### Equalities give rise to isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  iso-eq-Category : {x y : obj-Category C} → x ＝ y → iso-Category C x y
  iso-eq-Category {x} {y} = iso-eq-Precategory (precategory-Category C) x y

  preserves-concat-iso-eq-Category :
    {x y z : obj-Category C} (p : x ＝ y) (q : y ＝ z) →
    iso-eq-Category (p ∙ q) ＝
    comp-iso-Category C (iso-eq-Category q) (iso-eq-Category p)
  preserves-concat-iso-eq-Category refl q =
    inv (right-unit-law-comp-iso-Category C (iso-eq-Category q))
```

## Properties

### Extensionality of the type of objects in a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  extensionality-obj-Category :
    (x y : obj-Category C) → (x ＝ y) ≃ iso-Category C x y
  pr1 (extensionality-obj-Category x y) = iso-eq-Category C
  pr2 (extensionality-obj-Category x y) = is-category-Category C x y

  eq-iso-Category :
    {x y : obj-Category C} → iso-Category C x y → x ＝ y
  eq-iso-Category {x} {y} = map-inv-equiv (extensionality-obj-Category x y)

  is-section-eq-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    iso-eq-Category C (eq-iso-Category f) ＝ f
  is-section-eq-iso-Category {x} {y} =
    is-section-map-inv-equiv (extensionality-obj-Category x y)

  is-retraction-eq-iso-Category :
    {x y : obj-Category C} (p : x ＝ y) →
    eq-iso-Category (iso-eq-Category C p) ＝ p
  is-retraction-eq-iso-Category {x} {y} =
    is-retraction-map-inv-equiv (extensionality-obj-Category x y)

  preserves-comp-eq-iso-Category :
    { x y z : obj-Category C}
    ( g : iso-Category C y z)
    ( f : iso-Category C x y) →
    ( eq-iso-Category (comp-iso-Category C g f)) ＝
    ( (eq-iso-Category f ∙ eq-iso-Category g))
  preserves-comp-eq-iso-Category g f =
    equational-reasoning
      eq-iso-Category (comp-iso-Category C g f)
      ＝ eq-iso-Category
          ( comp-iso-Category C
            ( iso-eq-Category C (eq-iso-Category g))
            ( iso-eq-Category C (eq-iso-Category f)))
        by
          ap eq-iso-Category
            ( ap-binary
              ( comp-iso-Category C)
              ( inv (is-section-eq-iso-Category g))
              ( inv (is-section-eq-iso-Category f)))
      ＝ eq-iso-Category
          ( iso-eq-Category C (eq-iso-Category f ∙ eq-iso-Category g))
        by
          ap eq-iso-Category
            ( inv
              ( preserves-concat-iso-eq-Category C
                ( eq-iso-Category f)
                ( eq-iso-Category g)))
      ＝ eq-iso-Category f ∙ eq-iso-Category g
        by is-retraction-eq-iso-Category (eq-iso-Category f ∙ eq-iso-Category g)
```

### The type of isomorphisms forms a set

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-set-iso-Category : (x y : obj-Category C) → is-set (iso-Category C x y)
  is-set-iso-Category = is-set-iso-Precategory (precategory-Category C)

  iso-Category-Set : (x y : obj-Category C) → Set l2
  iso-Category-Set = iso-Precategory-Set (precategory-Category C)
```

### A morphism is an isomorphism if and only if precomposing by it is an equivalence

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  {x y : obj-Category C} (f : type-hom-Category C x y)
  where

{-
  is-equiv-precomp-is-iso-hom-Category :
    (H : is-iso-Category C f) →
    (z : obj-Category C) → is-equiv (precomp-iso-Category C {z = z} (pair f H))
  is-equiv-precomp-is-iso-hom-Category H z = {!!}
  -}
```
