# Isomorphism induction in categories

```agda
module category-theory.isomorphism-induction-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-categories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-systems
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.singleton-induction
```

</details>

## Idea

**Isomorphism induction** in a category `𝒞` is the principle asserting that for
any type family

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
  ev-id-iso-Category P f = f A (id-iso-Category C)

  induction-principle-iso-Category :
    {l : Level} (P : (B : obj-Category C) (e : iso-Category C A B) → UU l) →
    UU (l1 ⊔ l2 ⊔ l)
  induction-principle-iso-Category P = section (ev-id-iso-Category P)

  triangle-ev-id-iso-Category :
    {l : Level}
    (P : (Σ (obj-Category C) (iso-Category C A)) → UU l) →
    coherence-triangle-maps
      ( ev-point (A , id-iso-Category C) {P})
      ( ev-id-iso-Category (λ X e → P (X , e)))
      ( ev-pair {A = obj-Category C} {B = iso-Category C A} {C = P})
  triangle-ev-id-iso-Category P f = refl
```

## Properties

### Contractibility of the total space of isomorphisms implies isomorphism induction

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {A : obj-Category C}
  where

  abstract
    induction-principle-iso-is-contr-total-iso-Category :
      is-contr (Σ (obj-Category C) (iso-Category C A)) →
      {l : Level} →
      (P : (Σ (obj-Category C) (iso-Category C A)) → UU l) →
      induction-principle-iso-Category C (λ B e → P (B , e))
    induction-principle-iso-is-contr-total-iso-Category c P =
      section-left-factor
        ( ev-id-iso-Category C (λ X e → P (X , e)))
        ( ev-pair)
        ( is-singleton-is-contr
          ( A , id-iso-Category C)
          ( ( A , id-iso-Category C) ,
            ( λ t →
              inv (contraction c (A , id-iso-Category C)) ∙ contraction c t))
          ( P))
```

### Isomorphism induction implies contractibility of the total space of isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {A : obj-Category C}
  where

  abstract
    is-contr-total-equiv-induction-principle-iso-Category :
      ( {l : Level} (P : (Σ (obj-Category C) (iso-Category C A)) → UU l) →
        induction-principle-iso-Category C (λ B e → P (B , e))) →
      is-contr (Σ (obj-Category C) (iso-Category C A))
    is-contr-total-equiv-induction-principle-iso-Category ind =
      is-contr-is-singleton
        ( Σ (obj-Category C) (iso-Category C A))
        ( A , id-iso-Category C)
        ( λ P → section-comp
          ( ev-id-iso-Category C (λ X e → P (X , e)))
          ( ev-pair {A = obj-Category C} {B = iso-Category C A} {C = P})
          ( ind-Σ , refl-htpy)
          ( ind P))
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
      induction-principle-iso-is-contr-total-iso-Category C
        ( is-contr-total-iso-Category C _)
        ( λ t → P (pr1 t) (pr2 t))

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
    is-equiv-left-factor-htpy
      ( ev-point (A , id-iso-Category C))
      ( ev-id-iso-Category C P)
      ( ev-pair)
      ( triangle-ev-id-iso-Category C (λ u → P (pr1 u) (pr2 u)))
      ( dependent-universal-property-contr-is-contr
        ( A , id-iso-Category C)
        ( is-contr-total-iso-Category C A)
        ( λ u → P (pr1 u) (pr2 u)))
      ( is-equiv-ev-pair)

  is-contr-map-ev-id-iso-Category :
    is-contr-map (ev-id-iso-Category C P)
  is-contr-map-ev-id-iso-Category =
    is-contr-map-is-equiv is-equiv-ev-id-iso-Category
```
