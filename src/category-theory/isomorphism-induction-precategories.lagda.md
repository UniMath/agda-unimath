# Isomorphism induction in precategories

```agda
module category-theory.isomorphism-induction-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.sections
open import foundation.singleton-induction
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-identity-systems
open import foundation.universe-levels
```

</details>

## Idea

**Isomorphism induction** in a precategory `𝒞` is the principle asserting that,
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
  {l1 l2 : Level} (C : Precategory l1 l2) {A : obj-Precategory C}
  where

  ev-id-iso-Precategory :
    {l : Level} (P : (B : obj-Precategory C) → (iso-Precategory C A B) → UU l) →
    ((B : obj-Precategory C) (e : iso-Precategory C A B) → P B e) →
    P A (id-iso-Precategory C)
  ev-id-iso-Precategory P f = f A (id-iso-Precategory C)

  induction-principle-iso-Precategory :
    {l : Level} (P : (B : obj-Precategory C) → iso-Precategory C A B → UU l) →
    UU (l1 ⊔ l2 ⊔ l)
  induction-principle-iso-Precategory P = section (ev-id-iso-Precategory P)

  triangle-ev-id-iso-Precategory :
    {l : Level}
    (P : (B : obj-Precategory C) → iso-Precategory C A B → UU l) →
    coherence-triangle-maps
      ( ev-point (A , id-iso-Precategory C))
      ( ev-id-iso-Precategory P)
      ( ev-pair)
  triangle-ev-id-iso-Precategory P f = refl
```

## Properties

### Contractibility of the total space of isomorphisms implies isomorphism induction

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {A : obj-Precategory C}
  where

  abstract
    is-identity-system-iso-is-contr-total-iso-Precategory :
      is-contr (Σ (obj-Precategory C) (iso-Precategory C A)) →
      {l : Level} →
      is-identity-system l (iso-Precategory C A) A (id-iso-Precategory C)
    is-identity-system-iso-is-contr-total-iso-Precategory =
      is-identity-system-is-torsorial A (id-iso-Precategory C)
```

### Isomorphism induction implies contractibility of the total space of isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {A : obj-Precategory C}
  where

  is-contr-total-equiv-induction-principle-iso-Precategory :
    ( {l : Level} →
      is-identity-system l (iso-Precategory C A) A (id-iso-Precategory C)) →
    is-contr (Σ (obj-Precategory C) (iso-Precategory C A))
  is-contr-total-equiv-induction-principle-iso-Precategory =
    is-torsorial-is-identity-system A (id-iso-Precategory C)
```
