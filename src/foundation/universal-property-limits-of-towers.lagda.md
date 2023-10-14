# The universal property of limits of towers

```agda
module foundation.universal-property-limits-of-towers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.subtype-identity-principle
open import foundation.towers-of-types
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

## Definition

### The universal property of limits of towers

```agda
module _
  {l1 l2 : Level} (l : Level) (A : Tower l1) {X : UU l2}
  where

  universal-property-limit-Tower :
    (c : cone-Tower A X) → UU (l1 ⊔ l2 ⊔ lsuc l)
  universal-property-limit-Tower c =
    (Y : UU l) → is-equiv (cone-map-Tower A {Y = Y} c)
```

## Properties

### 3-for-2 property of limits of towers

```agda
module _
  {l1 l2 l3 : Level}
  {A : Tower l1} {X : UU l2} {Y : UU l3}
  (c : cone-Tower A X) (c' : cone-Tower A Y)
  (h : Y → X) (KLM : htpy-cone-Tower A (cone-map-Tower A c h) c')
  where

  inv-triangle-cone-cone-Tower :
    {l6 : Level} (D : UU l6) →
    cone-map-Tower A c ∘ postcomp D h ~ cone-map-Tower A c'
  inv-triangle-cone-cone-Tower D k =
    ap
      ( λ t → cone-map-Tower A t k)
      ( eq-htpy-cone-Tower A (cone-map-Tower A c h) c' KLM)

  triangle-cone-cone-Tower :
    {l6 : Level} (D : UU l6) →
    cone-map-Tower A c' ~ cone-map-Tower A c ∘ postcomp D h
  triangle-cone-cone-Tower D k = inv (inv-triangle-cone-cone-Tower D k)

  abstract
    is-equiv-up-limit-up-limit-Tower :
      ({l : Level} → universal-property-limit-Tower l A c) →
      ({l : Level} → universal-property-limit-Tower l A c') →
      is-equiv h
    is-equiv-up-limit-up-limit-Tower up up' =
      is-equiv-is-equiv-postcomp h
        ( λ D →
          is-equiv-right-factor-htpy
            ( cone-map-Tower A c')
            ( cone-map-Tower A c)
            ( postcomp D h)
            ( triangle-cone-cone-Tower D)
            ( up D)
            ( up' D))

  abstract
    up-limit-up-limit-is-equiv-Tower :
      is-equiv h →
      ({l : Level} → universal-property-limit-Tower l A c) →
      ({l : Level} → universal-property-limit-Tower l A c')
    up-limit-up-limit-is-equiv-Tower is-equiv-h up D =
      is-equiv-comp-htpy
        ( cone-map-Tower A c')
        ( cone-map-Tower A c)
        ( postcomp D h)
        ( triangle-cone-cone-Tower D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
        ( up D)

  abstract
    up-limit-is-equiv-up-limit-Tower :
      ({l : Level} → universal-property-limit-Tower l A c') →
      is-equiv h →
      ({l : Level} → universal-property-limit-Tower l A c)
    up-limit-is-equiv-up-limit-Tower up' is-equiv-h D =
      is-equiv-left-factor-htpy
        ( cone-map-Tower A c')
        ( cone-map-Tower A c)
        ( postcomp D h)
        ( triangle-cone-cone-Tower D)
        ( up' D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
```

### Uniqueness of maps obtained via the universal property of limits of towers

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2} (c : cone-Tower A X)
  where

  abstract
    uniqueness-universal-property-limit-Tower :
      ({l : Level} → universal-property-limit-Tower l A c) →
      {l3 : Level} (Y : UU l3) (c' : cone-Tower A Y) →
      is-contr (Σ (Y → X) (λ h → htpy-cone-Tower A (cone-map-Tower A c h) c'))
    uniqueness-universal-property-limit-Tower up Y c' =
      is-contr-equiv'
        ( Σ (Y → X) (λ h → cone-map-Tower A c h ＝ c'))
        ( equiv-tot
          ( λ h → extensionality-cone-Tower A (cone-map-Tower A c h) c'))
        ( is-contr-map-is-equiv (up Y) c')
```

### The universal property of limits of towers is a property

```agda
module _
  {l1 l2 l3 : Level} (A : Tower l1) {X : UU l2} (c : cone-Tower A X)
  where

  abstract
    is-prop-universal-property-limit-Tower :
      is-prop (universal-property-limit-Tower l3 A c)
    is-prop-universal-property-limit-Tower =
      is-prop-Π (λ Y → is-property-is-equiv (cone-map-Tower A c))

  map-universal-property-limit-Tower :
    ({l : Level} → universal-property-limit-Tower l A c) →
    {Y : UU l3} (c' : cone-Tower A Y) → Y → X
  map-universal-property-limit-Tower up-c {Y} c' =
    map-inv-is-equiv (up-c Y) c'

  eq-map-universal-property-limit-Tower :
    (up-c : {l : Level} → universal-property-limit-Tower l A c) →
    {Y : UU l3} (c' : cone-Tower A Y) →
    cone-map-Tower A c (map-universal-property-limit-Tower up-c c') ＝ c'
  eq-map-universal-property-limit-Tower up-c {Y} c' =
    is-section-map-inv-is-equiv (up-c Y) c'
```

### The homotopy of cones obtained from the universal property of limits of towers

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  htpy-cone-map-universal-property-limit-Tower :
    (c : cone-Tower A X)
    (up : {l : Level} → universal-property-limit-Tower l A c) →
    {l3 : Level} {Y : UU l3} (c' : cone-Tower A Y) →
    htpy-cone-Tower A
      ( cone-map-Tower A c (map-universal-property-limit-Tower A c up c'))
      ( c')
  htpy-cone-map-universal-property-limit-Tower c up c' =
    htpy-eq-cone-Tower A
      ( cone-map-Tower A c (map-universal-property-limit-Tower A c up c'))
      ( c')
      ( eq-map-universal-property-limit-Tower A c up c')
```

### Unique uniqueness of limits of towers

```agda
module _
  {l1 l2 l3 : Level} (A : Tower l1) {X : UU l2} {Y : UU l3}
  where

  abstract
    uniquely-unique-pullback :
      ( c' : cone-Tower A Y) (c : cone-Tower A X) →
      ( up-c' : {l : Level} → universal-property-limit-Tower l A c') →
      ( up-c : {l : Level} → universal-property-limit-Tower l A c) →
      is-contr
        ( Σ (Y ≃ X)
            ( λ e → htpy-cone-Tower A (cone-map-Tower A c (map-equiv e)) c'))
    uniquely-unique-pullback c' c up-c' up-c =
      is-contr-total-Eq-subtype
        ( uniqueness-universal-property-limit-Tower A c up-c Y c')
        ( is-property-is-equiv)
        ( map-universal-property-limit-Tower A c up-c c')
        ( htpy-cone-map-universal-property-limit-Tower A c up-c c')
        ( is-equiv-up-limit-up-limit-Tower c c'
          ( map-universal-property-limit-Tower A c up-c c')
          ( htpy-cone-map-universal-property-limit-Tower A c up-c c')
          up-c up-c')
```
