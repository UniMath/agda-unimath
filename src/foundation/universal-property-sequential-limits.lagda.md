# The universal property of sequential limits

```agda
module foundation.universal-property-sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.postcomposition-functions
open import foundation.subtype-identity-principle
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given a [tower of types](foundation.towers.md)

```text
               fₙ                     f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀
```

the **sequential limit** `limₙ Aₙ` is a universal type completing the diagram

```text
                           fₙ                     f₁      f₀
  limₙ Aₙ ---> ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

The **universal property of the sequential limit** states that `limₙ Aₙ` is the
terminal such type, by which we mean that given any
[cone](foundation.cones-over-towers.md) over `A` with domain `X`, there is a
[unique](foundation-core.contractible-types.md) map `g : X → limₙ Aₙ` exhibiting
that cone as a composite of `g` with the cone of `limₙ Aₙ` over `A`.

## Definition

### The universal property of sequential limits

```agda
module _
  {l1 l2 : Level} (l : Level) (A : tower l1) {X : UU l2}
  where

  universal-property-sequential-limit :
    (c : cone-tower A X) → UU (l1 ⊔ l2 ⊔ lsuc l)
  universal-property-sequential-limit c =
    (Y : UU l) → is-equiv (cone-map-tower A {Y = Y} c)

module _
  {l1 l2 l3 : Level} (A : tower l1) {X : UU l2} (c : cone-tower A X)
  where

  map-universal-property-sequential-limit :
    ({l : Level} → universal-property-sequential-limit l A c) →
    {Y : UU l3} (c' : cone-tower A Y) → Y → X
  map-universal-property-sequential-limit up-c {Y} c' =
    map-inv-is-equiv (up-c Y) c'

  compute-map-universal-property-sequential-limit :
    (up-c : {l : Level} → universal-property-sequential-limit l A c) →
    {Y : UU l3} (c' : cone-tower A Y) →
    cone-map-tower A c (map-universal-property-sequential-limit up-c c') ＝ c'
  compute-map-universal-property-sequential-limit up-c {Y} c' =
    is-section-map-inv-is-equiv (up-c Y) c'
```

## Properties

### 3-for-2 property of sequential limits

```agda
module _
  {l1 l2 l3 : Level}
  {A : tower l1} {X : UU l2} {Y : UU l3}
  (c : cone-tower A X) (c' : cone-tower A Y)
  (h : Y → X) (KLM : htpy-cone-tower A (cone-map-tower A c h) c')
  where

  inv-triangle-cone-cone-tower :
    {l6 : Level} (D : UU l6) →
    cone-map-tower A c ∘ postcomp D h ~ cone-map-tower A c'
  inv-triangle-cone-cone-tower D k =
    ap
      ( λ t → cone-map-tower A t k)
      ( eq-htpy-cone-tower A (cone-map-tower A c h) c' KLM)

  triangle-cone-cone-tower :
    {l6 : Level} (D : UU l6) →
    cone-map-tower A c' ~ cone-map-tower A c ∘ postcomp D h
  triangle-cone-cone-tower D k = inv (inv-triangle-cone-cone-tower D k)

  abstract
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limit :
      ({l : Level} → universal-property-sequential-limit l A c) →
      ({l : Level} → universal-property-sequential-limit l A c') →
      is-equiv h
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limit
      up up' =
      is-equiv-is-equiv-postcomp h
        ( λ D →
          is-equiv-top-map-triangle
            ( cone-map-tower A c')
            ( cone-map-tower A c)
            ( postcomp D h)
            ( triangle-cone-cone-tower D)
            ( up D)
            ( up' D))

  abstract
    universal-property-sequential-limit-universal-property-sequential-limit-is-equiv :
      is-equiv h →
      ({l : Level} → universal-property-sequential-limit l A c) →
      ({l : Level} → universal-property-sequential-limit l A c')
    universal-property-sequential-limit-universal-property-sequential-limit-is-equiv
      is-equiv-h up D =
      is-equiv-left-map-triangle
        ( cone-map-tower A c')
        ( cone-map-tower A c)
        ( postcomp D h)
        ( triangle-cone-cone-tower D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
        ( up D)

  abstract
    universal-property-sequential-limit-is-equiv-universal-property-sequential-limit :
      ({l : Level} → universal-property-sequential-limit l A c') →
      is-equiv h →
      ({l : Level} → universal-property-sequential-limit l A c)
    universal-property-sequential-limit-is-equiv-universal-property-sequential-limit
      up' is-equiv-h D =
      is-equiv-right-map-triangle
        ( cone-map-tower A c')
        ( cone-map-tower A c)
        ( postcomp D h)
        ( triangle-cone-cone-tower D)
        ( up' D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
```

### Uniqueness of maps obtained via the universal property of sequential limits

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2} (c : cone-tower A X)
  where

  abstract
    uniqueness-universal-property-sequential-limit :
      ({l : Level} → universal-property-sequential-limit l A c) →
      {l3 : Level} (Y : UU l3) (c' : cone-tower A Y) →
      is-contr (Σ (Y → X) (λ h → htpy-cone-tower A (cone-map-tower A c h) c'))
    uniqueness-universal-property-sequential-limit up Y c' =
      is-contr-equiv'
        ( Σ (Y → X) (λ h → cone-map-tower A c h ＝ c'))
        ( equiv-tot
          ( λ h → extensionality-cone-tower A (cone-map-tower A c h) c'))
        ( is-contr-map-is-equiv (up Y) c')
```

### The universal property of sequential limits at a universe level is a property

```agda
module _
  {l1 l2 l3 : Level} (A : tower l1) {X : UU l2} (c : cone-tower A X)
  where

  abstract
    is-prop-universal-property-sequential-limit :
      is-prop (universal-property-sequential-limit l3 A c)
    is-prop-universal-property-sequential-limit =
      is-prop-Π (λ Y → is-property-is-equiv (cone-map-tower A c))
```

### The homotopy of cones obtained from the universal property of sequential limits

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  htpy-cone-map-universal-property-sequential-limit :
    (c : cone-tower A X)
    (up : {l : Level} → universal-property-sequential-limit l A c) →
    {l3 : Level} {Y : UU l3} (c' : cone-tower A Y) →
    htpy-cone-tower A
      ( cone-map-tower A c (map-universal-property-sequential-limit A c up c'))
      ( c')
  htpy-cone-map-universal-property-sequential-limit c up c' =
    htpy-eq-cone-tower A
      ( cone-map-tower A c (map-universal-property-sequential-limit A c up c'))
      ( c')
      ( compute-map-universal-property-sequential-limit A c up c')
```

### Unique uniqueness of sequential limits

```agda
module _
  {l1 l2 l3 : Level} (A : tower l1) {X : UU l2} {Y : UU l3}
  where

  abstract
    uniquely-unique-sequential-limit :
      ( c' : cone-tower A Y) (c : cone-tower A X) →
      ( up-c' : {l : Level} → universal-property-sequential-limit l A c') →
      ( up-c : {l : Level} → universal-property-sequential-limit l A c) →
      is-contr
        ( Σ (Y ≃ X)
            ( λ e → htpy-cone-tower A (cone-map-tower A c (map-equiv e)) c'))
    uniquely-unique-sequential-limit c' c up-c' up-c =
      is-torsorial-Eq-subtype
        ( uniqueness-universal-property-sequential-limit A c up-c Y c')
        ( is-property-is-equiv)
        ( map-universal-property-sequential-limit A c up-c c')
        ( htpy-cone-map-universal-property-sequential-limit A c up-c c')
        ( is-equiv-universal-property-sequential-limit-universal-property-sequential-limit
          ( c)
          ( c')
          ( map-universal-property-sequential-limit A c up-c c')
          ( htpy-cone-map-universal-property-sequential-limit A c up-c c')
          ( up-c)
          ( up-c'))
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}

## See also

- For sequential colimits, see
  [`synthetic-homotopy-theory.universal-property-sequential-colimits`](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
