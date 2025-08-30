# Sequential limits

```agda
module foundation.sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cones-over-inverse-sequential-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inverse-sequential-diagrams
open import foundation.structure-identity-principle
open import foundation.universal-property-sequential-limits
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given an
[inverse sequential diagram of types](foundation.inverse-sequential-diagrams.md)

```text
               fₙ                     f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀
```

we can form the **standard sequential limit** `limₙ Aₙ` satisfying
[the universal property of the sequential limit](foundation.universal-property-sequential-limits.md)
of `Aₙ` thus completing the diagram

```text
                           fₙ                     f₁      f₀
  limₙ Aₙ ---> ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

The standard sequential limit consists of "points at infinity", which can be
recorded as [sequences](lists.dependent-sequences.md) of terms whose images
under `f` agree:

```text
  ⋯  ↦   xₙ₊₁  ↦   xₙ  ↦   ⋯  ↦   x₂  ↦   x₁  ↦   x₀
          ⫙        ⫙              ⫙       ⫙       ⫙
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

## Definitions

### The standard sequential limit

```agda
module _
  {l : Level} (A : inverse-sequential-diagram l)
  where

  standard-sequential-limit : UU l
  standard-sequential-limit =
    Σ ( (n : ℕ) → family-inverse-sequential-diagram A n)
      ( λ a → (n : ℕ) → a n ＝ map-inverse-sequential-diagram A n (a (succ-ℕ n)))

module _
  {l : Level} (A : inverse-sequential-diagram l)
  where

  sequence-standard-sequential-limit :
    standard-sequential-limit A → (n : ℕ) →
    family-inverse-sequential-diagram A n
  sequence-standard-sequential-limit = pr1

  coherence-standard-sequential-limit :
    (x : standard-sequential-limit A) (n : ℕ) →
    sequence-standard-sequential-limit x n ＝
    map-inverse-sequential-diagram A n
      ( sequence-standard-sequential-limit x (succ-ℕ n))
  coherence-standard-sequential-limit = pr2
```

### The cone at the standard sequential limit

```agda
module _
  {l : Level} (A : inverse-sequential-diagram l)
  where

  cone-standard-sequential-limit :
    cone-inverse-sequential-diagram A (standard-sequential-limit A)
  pr1 cone-standard-sequential-limit n x =
    sequence-standard-sequential-limit A x n
  pr2 cone-standard-sequential-limit n x =
    coherence-standard-sequential-limit A x n
```

### The gap map into the standard sequential limit

The **gap map** of a
[cone over an inverse sequential diagram](foundation.cones-over-inverse-sequential-diagrams.md)
is the map from the domain of the cone into the standard sequential limit.

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) {X : UU l2}
  where

  gap-inverse-sequential-diagram :
    cone-inverse-sequential-diagram A X → X → standard-sequential-limit A
  pr1 (gap-inverse-sequential-diagram c x) n =
    map-cone-inverse-sequential-diagram A c n x
  pr2 (gap-inverse-sequential-diagram c x) n =
    coherence-cone-inverse-sequential-diagram A c n x
```

### The property of being a sequential limit

The [proposition](foundation-core.propositions.md) `is-sequential-limit` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation.universal-property-sequential-limits.md) is
a large proposition.

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) {X : UU l2}
  where

  is-sequential-limit : cone-inverse-sequential-diagram A X → UU (l1 ⊔ l2)
  is-sequential-limit c = is-equiv (gap-inverse-sequential-diagram A c)

  is-property-is-sequential-limit :
    (c : cone-inverse-sequential-diagram A X) → is-prop (is-sequential-limit c)
  is-property-is-sequential-limit c =
    is-property-is-equiv (gap-inverse-sequential-diagram A c)

  is-sequential-limit-Prop :
    (c : cone-inverse-sequential-diagram A X) → Prop (l1 ⊔ l2)
  pr1 (is-sequential-limit-Prop c) = is-sequential-limit c
  pr2 (is-sequential-limit-Prop c) = is-property-is-sequential-limit c
```

## Properties

### Characterization of equality in the standard sequential limit

```agda
module _
  {l : Level} (A : inverse-sequential-diagram l)
  where

  coherence-Eq-standard-sequential-limit :
    (s t : standard-sequential-limit A)
    (H :
      sequence-standard-sequential-limit A s ~
      sequence-standard-sequential-limit A t) → UU l
  coherence-Eq-standard-sequential-limit s t H =
    coherence-square-homotopies
      ( H)
      ( coherence-standard-sequential-limit A s)
      ( coherence-standard-sequential-limit A t)
      ( λ n → ap (map-inverse-sequential-diagram A n) (H (succ-ℕ n)))

  Eq-standard-sequential-limit : (s t : standard-sequential-limit A) → UU l
  Eq-standard-sequential-limit s t =
    Σ ( sequence-standard-sequential-limit A s ~
        sequence-standard-sequential-limit A t)
      ( coherence-Eq-standard-sequential-limit s t)

  refl-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) → Eq-standard-sequential-limit s s
  pr1 (refl-Eq-standard-sequential-limit s) = refl-htpy
  pr2 (refl-Eq-standard-sequential-limit s) = right-unit-htpy

  Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    s ＝ t → Eq-standard-sequential-limit s t
  Eq-eq-standard-sequential-limit s .s refl =
    refl-Eq-standard-sequential-limit s

  is-torsorial-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) →
    is-torsorial (Eq-standard-sequential-limit s)
  is-torsorial-Eq-standard-sequential-limit s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (pr1 s))
      ( pr1 s , refl-htpy)
      ( is-torsorial-Eq-Π (λ n → is-torsorial-Id (pr2 s n ∙ refl)))

  is-equiv-Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    is-equiv (Eq-eq-standard-sequential-limit s t)
  is-equiv-Eq-eq-standard-sequential-limit s =
    fundamental-theorem-id
      ( is-torsorial-Eq-standard-sequential-limit s)
      ( Eq-eq-standard-sequential-limit s)

  extensionality-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    (s ＝ t) ≃ Eq-standard-sequential-limit s t
  pr1 (extensionality-standard-sequential-limit s t) =
    Eq-eq-standard-sequential-limit s t
  pr2 (extensionality-standard-sequential-limit s t) =
    is-equiv-Eq-eq-standard-sequential-limit s t

  eq-Eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    Eq-standard-sequential-limit s t → s ＝ t
  eq-Eq-standard-sequential-limit s t =
    map-inv-equiv (extensionality-standard-sequential-limit s t)
```

### The standard sequential limit satisfies the universal property of a sequential limit

```agda
module _
  {l1 : Level} (A : inverse-sequential-diagram l1)
  where

  cone-map-standard-sequential-limit :
    {l : Level} {Y : UU l} →
    (Y → standard-sequential-limit A) → cone-inverse-sequential-diagram A Y
  cone-map-standard-sequential-limit {Y = Y} =
    cone-map-inverse-sequential-diagram A {Y = Y}
      ( cone-standard-sequential-limit A)

  is-retraction-gap-inverse-sequential-diagram :
    {l : Level} {Y : UU l} →
    is-retraction
      ( cone-map-standard-sequential-limit {Y = Y})
      ( gap-inverse-sequential-diagram A)
  is-retraction-gap-inverse-sequential-diagram = refl-htpy

  is-section-gap-inverse-sequential-diagram :
    {l : Level} {Y : UU l} →
    is-section
      ( cone-map-standard-sequential-limit {Y = Y})
      ( gap-inverse-sequential-diagram A)
  is-section-gap-inverse-sequential-diagram = refl-htpy

  up-standard-sequential-limit :
    universal-property-sequential-limit A (cone-standard-sequential-limit A)
  pr1 (pr1 (up-standard-sequential-limit X)) =
    gap-inverse-sequential-diagram A
  pr2 (pr1 (up-standard-sequential-limit X)) =
    is-section-gap-inverse-sequential-diagram
  pr1 (pr2 (up-standard-sequential-limit X)) =
    gap-inverse-sequential-diagram A
  pr2 (pr2 (up-standard-sequential-limit X)) =
    is-retraction-gap-inverse-sequential-diagram
```

### A cone over an inverse sequential diagram is equal to the value of `cone-map-inverse-sequential-diagram` at its own gap map

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) {X : UU l2}
  (c : cone-inverse-sequential-diagram A X)
  where

  htpy-cone-up-sequential-limit-standard-sequential-limit :
    htpy-cone-inverse-sequential-diagram A
      ( cone-map-inverse-sequential-diagram A
        ( cone-standard-sequential-limit A)
        ( gap-inverse-sequential-diagram A c))
      ( c)
  pr1 htpy-cone-up-sequential-limit-standard-sequential-limit n = refl-htpy
  pr2 htpy-cone-up-sequential-limit-standard-sequential-limit n =
    right-unit-htpy
```

### A cone satisfies the universal property of the sequential limit if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) {X : UU l2}
  (c : cone-inverse-sequential-diagram A X)
  where

  is-sequential-limit-universal-property-sequential-limit :
    universal-property-sequential-limit A c → is-sequential-limit A c
  is-sequential-limit-universal-property-sequential-limit =
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limit
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-inverse-sequential-diagram A c)
      ( htpy-cone-up-sequential-limit-standard-sequential-limit A c)
      ( up-standard-sequential-limit A)

  universal-property-is-sequential-limit :
    is-sequential-limit A c → universal-property-sequential-limit A c
  universal-property-is-sequential-limit is-lim-c =
    universal-property-sequential-limit-universal-property-sequential-limit-is-equiv
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-inverse-sequential-diagram A c)
      ( htpy-cone-up-sequential-limit-standard-sequential-limit A c)
      ( is-lim-c)
      ( up-standard-sequential-limit A)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
