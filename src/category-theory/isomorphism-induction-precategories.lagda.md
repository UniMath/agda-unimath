# Isomorphism induction in precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.isomorphism-induction-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext

open import foundation.commuting-triangles-of-maps funext
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.identity-systems
open import foundation.identity-types funext
open import foundation.sections funext
open import foundation.torsorial-type-families funext
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
categories, hence this is one approach to proving that a precategory is a
category.

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
    is-identity-system-is-torsorial-iso-Precategory :
      is-torsorial (iso-Precategory C A) →
      is-identity-system (iso-Precategory C A) A (id-iso-Precategory C)
    is-identity-system-is-torsorial-iso-Precategory =
      is-identity-system-is-torsorial A (id-iso-Precategory C)
```

### Isomorphism induction implies contractibility of the total space of isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {A : obj-Precategory C}
  where

  is-torsorial-equiv-induction-principle-iso-Precategory :
    is-identity-system (iso-Precategory C A) A (id-iso-Precategory C) →
    is-torsorial (iso-Precategory C A)
  is-torsorial-equiv-induction-principle-iso-Precategory =
    is-torsorial-is-identity-system A (id-iso-Precategory C)
```
