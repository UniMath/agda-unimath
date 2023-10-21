# Isomorphism induction in categories

```agda
module category-theory.isomorphism-induction-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphism-induction-precategories
open import category-theory.isomorphisms-in-categories

open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.sections
open import foundation.universal-property-identity-systems
open import foundation.universe-levels
```

</details>

## Idea

**Isomorphism induction** in a category `𝒞` is the principle asserting that,
given an object `A : 𝒞` and any type family

```text
  P : (B : 𝒞) (ϕ : A ≅ B) → 𝒰
```

of types indexed by all
[isomorphisms](category-theory.isomorphisms-in-categories.md) with domain `A`,
there is a [section](foundation.sections.md) of the evaluation map

```text
  ((B : 𝒞) (ϕ : A ≅ B) → P B ϕ) → P A id-iso.
```

The principle of isomorphism induction is equivalent to the univalence axiom for
categories.

## Statement

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {A : obj-Category C}
  where

  ev-id-iso-Category :
    {l : Level} (P : (B : obj-Category C) → (iso-Category C A B) → UU l) →
    ((B : obj-Category C) (e : iso-Category C A B) → P B e) →
    P A (id-iso-Category C)
  ev-id-iso-Category = ev-id-iso-Precategory (precategory-Category C)

  induction-principle-iso-Category :
    {l : Level} (P : (B : obj-Category C) (e : iso-Category C A B) → UU l) →
    UU (l1 ⊔ l2 ⊔ l)
  induction-principle-iso-Category =
    induction-principle-iso-Precategory (precategory-Category C)

  triangle-ev-id-iso-Category :
    {l : Level}
    (P : (B : obj-Category C) → iso-Category C A B → UU l) →
    coherence-triangle-maps
      ( ev-point (A , id-iso-Category C))
      ( ev-id-iso-Category P)
      ( ev-pair)
  triangle-ev-id-iso-Category =
    triangle-ev-id-iso-Precategory (precategory-Category C)
```

## Properties

### Contractibility of the total space of isomorphisms implies isomorphism induction

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {A : obj-Category C}
  where

  abstract
    is-identity-system-iso-is-torsorial-iso-Category :
      is-contr (Σ (obj-Category C) (iso-Category C A)) →
      {l : Level} →
      is-identity-system l (iso-Category C A) A (id-iso-Category C)
    is-identity-system-iso-is-torsorial-iso-Category =
      is-identity-system-iso-is-torsorial-iso-Precategory
        ( precategory-Category C)
```

### Isomorphism induction implies contractibility of the total space of isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {A : obj-Category C}
  where

  is-torsorial-equiv-induction-principle-iso-Category :
    ( {l : Level} →
      is-identity-system l (iso-Category C A) A (id-iso-Category C)) →
    is-contr (Σ (obj-Category C) (iso-Category C A))
  is-torsorial-equiv-induction-principle-iso-Category =
    is-torsorial-equiv-induction-principle-iso-Precategory
      ( precategory-Category C)
```

### Isomorphism induction in a category

```agda
module _
  {l1 l2 l3 : Level} (C : Category l1 l2) {A : obj-Category C}
  (P : (B : obj-Category C) (e : iso-Category C A B) → UU l3)
  where

  abstract
    is-identity-system-iso-Category : section (ev-id-iso-Category C P)
    is-identity-system-iso-Category =
      is-identity-system-iso-is-torsorial-iso-Category C
        ( is-torsorial-iso-Category C A) P

  ind-iso-Category :
    P A (id-iso-Category C) →
    {B : obj-Category C} (e : iso-Category C A B) → P B e
  ind-iso-Category p {B} = pr1 is-identity-system-iso-Category p B

  compute-ind-iso-Category :
    (u : P A (id-iso-Category C)) → ind-iso-Category u (id-iso-Category C) ＝ u
  compute-ind-iso-Category = pr2 is-identity-system-iso-Category
```

### The evaluation map `ev-id-iso-Category` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} (C : Category l1 l2) {A : obj-Category C}
  (P : (B : obj-Category C) (e : iso-Category C A B) → UU l3)
  where

  is-equiv-ev-id-iso-Category : is-equiv (ev-id-iso-Category C P)
  is-equiv-ev-id-iso-Category =
    dependent-universal-property-identity-system-is-torsorial
      ( id-iso-Category C)
      ( is-torsorial-iso-Category C A)
      ( P)

  is-contr-map-ev-id-iso-Category :
    is-contr-map (ev-id-iso-Category C P)
  is-contr-map-ev-id-iso-Category =
    is-contr-map-is-equiv is-equiv-ev-id-iso-Category
```
