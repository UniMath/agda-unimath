---
title: Slice precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.slice-precategories where

open import category-theory.precategories

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-inv-equiv)
open import foundation.identity-types using (_＝_; refl; inv; _∙_; ap)
open import foundation.sets using
  ( Set; Σ-Set; set-Prop; Id-Prop; type-Set; is-set; is-set-type-Set)
open import foundation.subtypes using
  ( extensionality-type-subtype')
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The slice precategory of a precategory `C` over an object `X` of `C` is the category of objects of `C` equipped with a morphism into `X`.

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (X : obj-Precat C)
  where

  obj-slice-Precat : UU (l1 ⊔ l2)
  obj-slice-Precat = Σ (obj-Precat C) (λ A → type-hom-Precat C A X)

  hom-slice-Precat : obj-slice-Precat → obj-slice-Precat → Set l2
  hom-slice-Precat (pair A f) (pair B g) =
    Σ-Set
      ( hom-Precat C A B)
      ( λ h → set-Prop (Id-Prop (hom-Precat C A X) f (comp-hom-Precat C g h)))

  type-hom-slice-Precat : obj-slice-Precat → obj-slice-Precat → UU l2
  type-hom-slice-Precat A B = type-Set (hom-slice-Precat A B)

  is-set-type-hom-slice-Precat :
    (A B : obj-slice-Precat) → is-set (type-hom-slice-Precat A B)
  is-set-type-hom-slice-Precat A B = is-set-type-Set (hom-slice-Precat A B)

  Eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) → UU l2
  Eq-hom-slice-Precat f g = (pr1 f ＝ pr1 g)

  refl-Eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    Eq-hom-slice-Precat f f
  refl-Eq-hom-slice-Precat f = refl

  extensionality-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) →
    (f ＝ g) ≃ Eq-hom-slice-Precat f g
  extensionality-hom-slice-Precat {A} {B} =
    extensionality-type-subtype'
      ( λ h →
        Id-Prop (hom-Precat C (pr1 A) X) (pr2 A) (comp-hom-Precat C (pr2 B) h))

  eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) →
    Eq-hom-slice-Precat f g → f ＝ g
  eq-hom-slice-Precat f g =
    map-inv-equiv (extensionality-hom-slice-Precat f g)
```

### Identity morphisms in the slice category

```agda
  id-hom-slice-Precat :
    (A : obj-slice-Precat) → type-hom-slice-Precat A A
  pr1 (id-hom-slice-Precat A) = id-hom-Precat C
  pr2 (id-hom-slice-Precat A) = inv (right-unit-law-comp-hom-Precat C (pr2 A))
```

### Composition of morphisms in the slice category

```agda
  comp-hom-slice-Precat :
    {A1 A2 A3 : obj-slice-Precat} →
    type-hom-slice-Precat A2 A3 → type-hom-slice-Precat A1 A2 →
    type-hom-slice-Precat A1 A3
  pr1 (comp-hom-slice-Precat g f) = comp-hom-Precat C (pr1 g) (pr1 f)
  pr2 (comp-hom-slice-Precat g f) =
    ( pr2 f) ∙
    ( ( ap (λ u → comp-hom-Precat C u (pr1 f)) (pr2 g)) ∙
      ( assoc-comp-hom-Precat C _ (pr1 g) (pr1 f)))
```

### Associativity of composition of morphisms in the slice category

```agda
  assoc-comp-hom-slice-Precat :
    {A1 A2 A3 A4 : obj-slice-Precat} →
    (h : type-hom-slice-Precat A3 A4) (g : type-hom-slice-Precat A2 A3)
    (f : type-hom-slice-Precat A1 A2) →
    ( comp-hom-slice-Precat (comp-hom-slice-Precat h g) f) ＝
    ( comp-hom-slice-Precat h (comp-hom-slice-Precat g f))
  assoc-comp-hom-slice-Precat h g f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat (comp-hom-slice-Precat h g) f)
      ( comp-hom-slice-Precat h (comp-hom-slice-Precat g f))
      ( assoc-comp-hom-Precat C (pr1 h) (pr1 g) (pr1 f))
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    comp-hom-slice-Precat (id-hom-slice-Precat B) f ＝ f
  left-unit-law-comp-hom-slice-Precat f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat (id-hom-slice-Precat _) f)
      ( f)
      ( left-unit-law-comp-hom-Precat C (pr1 f))
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    comp-hom-slice-Precat f (id-hom-slice-Precat A) ＝ f
  right-unit-law-comp-hom-slice-Precat f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat f (id-hom-slice-Precat _))
      ( f)
      ( right-unit-law-comp-hom-Precat C (pr1 f))
```

### The slice precategory

```agda
  slice-Precat : Precat (l1 ⊔ l2) l2
  pr1 slice-Precat = obj-slice-Precat
  pr1 (pr2 slice-Precat) = hom-slice-Precat
  pr1 (pr1 (pr2 (pr2 slice-Precat))) = comp-hom-slice-Precat
  pr2 (pr1 (pr2 (pr2 slice-Precat))) = assoc-comp-hom-slice-Precat
  pr1 (pr2 (pr2 (pr2 slice-Precat))) = id-hom-slice-Precat
  pr1 (pr2 (pr2 (pr2 (pr2 slice-Precat)))) = left-unit-law-comp-hom-slice-Precat
  pr2 (pr2 (pr2 (pr2 (pr2 slice-Precat)))) =
    right-unit-law-comp-hom-slice-Precat
```
