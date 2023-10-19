# Dependent cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Definitions

### Dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) (P : X → UU l3)
  where

  dependent-cocone-sequential-diagram : UU (l1 ⊔ l3)
  dependent-cocone-sequential-diagram =
    Σ ( ( n : ℕ) (a : family-sequential-diagram A n) →
        P (map-cocone-sequential-diagram A c n a))
      ( λ i →
        ( n : ℕ) → (a : family-sequential-diagram A n) →
        dependent-identification P
          ( coherence-triangle-cocone-sequential-diagram A c n a)
          ( i n a)
          ( i (succ-ℕ n) (map-sequential-diagram A n a)))
```

### Components of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  ( d : dependent-cocone-sequential-diagram A c P)
  where

  map-dependent-cocone-sequential-diagram :
    ( n : ℕ) (a : family-sequential-diagram A n) →
    P (map-cocone-sequential-diagram A c n a)
  map-dependent-cocone-sequential-diagram = pr1 d

  coherence-triangle-dependent-cocone-sequential-diagram :
    ( n : ℕ) → (a : family-sequential-diagram A n) →
    dependent-identification P
      ( coherence-triangle-cocone-sequential-diagram A c n a)
      ( map-dependent-cocone-sequential-diagram n a)
      ( map-dependent-cocone-sequential-diagram
        ( succ-ℕ n)
        ( map-sequential-diagram A n a))
  coherence-triangle-dependent-cocone-sequential-diagram = pr2 d
```

### Homotopies of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  coherence-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( K :
      ( n : ℕ) →
      ( map-dependent-cocone-sequential-diagram A P d n) ~
      ( map-dependent-cocone-sequential-diagram A P d' n)) →
    UU (l1 ⊔ l3)
  coherence-htpy-dependent-cocone-sequential-diagram d d' K =
    ( n : ℕ) (a : family-sequential-diagram A n) →
    ( ( coherence-triangle-dependent-cocone-sequential-diagram A P d n a) ∙
      ( K (succ-ℕ n) (map-sequential-diagram A n a))) ＝
    ( ( ap
        ( tr P (coherence-triangle-cocone-sequential-diagram A c n a))
        ( K n a)) ∙
      ( coherence-triangle-dependent-cocone-sequential-diagram A P d' n a))

  htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    UU (l1 ⊔ l3)
  htpy-dependent-cocone-sequential-diagram d d' =
    Σ ( ( n : ℕ) →
        ( map-dependent-cocone-sequential-diagram A P d n) ~
        ( map-dependent-cocone-sequential-diagram A P d' n))
      ( coherence-htpy-dependent-cocone-sequential-diagram d d')
```

### Components of homotopies of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  ( d d' : dependent-cocone-sequential-diagram A c P)
  ( H : htpy-dependent-cocone-sequential-diagram A P d d')
  where

  htpy-htpy-dependent-cocone-sequential-diagram :
    ( n : ℕ) →
    ( map-dependent-cocone-sequential-diagram A P d n) ~
    ( map-dependent-cocone-sequential-diagram A P d' n)
  htpy-htpy-dependent-cocone-sequential-diagram = pr1 H

  coherence-htpy-htpy-dependent-cocone-sequential-diagram :
    coherence-htpy-dependent-cocone-sequential-diagram A P d d'
      ( htpy-htpy-dependent-cocone-sequential-diagram)
  coherence-htpy-htpy-dependent-cocone-sequential-diagram = pr2 H
```

### Obtaining dependent cocones under sequential diagrams by postcomposing cocones under sequential diagrams with dependent maps

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-cocone-map-sequential-diagram :
    { l : Level} (P : X → UU l) →
    ( (x : X) → P x) → dependent-cocone-sequential-diagram A c P
  pr1 (dependent-cocone-map-sequential-diagram P h) n =
    h ∘ map-cocone-sequential-diagram A c n
  pr2 (dependent-cocone-map-sequential-diagram P h) n =
    apd h ∘ coherence-triangle-cocone-sequential-diagram A c n
```

## Properties

### Characterization of identity types of cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  reflexive-htpy-dependent-cocone-sequential-diagram :
    ( d : dependent-cocone-sequential-diagram A c P) →
    htpy-dependent-cocone-sequential-diagram A P d d
  pr1 (reflexive-htpy-dependent-cocone-sequential-diagram d) n = refl-htpy
  pr2 (reflexive-htpy-dependent-cocone-sequential-diagram d) n = right-unit-htpy

  htpy-eq-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( d ＝ d') → htpy-dependent-cocone-sequential-diagram A P d d'
  htpy-eq-dependent-cocone-sequential-diagram d .d refl =
    reflexive-htpy-dependent-cocone-sequential-diagram d

  abstract
    is-torsorial-htpy-dependent-cocone-sequential-diagram :
      ( d : dependent-cocone-sequential-diagram A c P) →
      is-contr
        ( Σ ( dependent-cocone-sequential-diagram A c P)
            ( htpy-dependent-cocone-sequential-diagram A P d))
    is-torsorial-htpy-dependent-cocone-sequential-diagram d =
      is-torsorial-Eq-structure
        ( ev-pair (coherence-htpy-dependent-cocone-sequential-diagram A P d))
        ( is-torsorial-binary-htpy
          ( map-dependent-cocone-sequential-diagram A P d))
        ( map-dependent-cocone-sequential-diagram A P d ,
          ev-pair refl-htpy)
        ( is-torsorial-binary-htpy
          ( λ n →
            ( coherence-triangle-dependent-cocone-sequential-diagram A P d n) ∙h
            ( refl-htpy)))

    is-equiv-htpy-eq-dependent-cocone-sequential-diagram :
      ( d d' : dependent-cocone-sequential-diagram A c P) →
      is-equiv (htpy-eq-dependent-cocone-sequential-diagram d d')
    is-equiv-htpy-eq-dependent-cocone-sequential-diagram d =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cocone-sequential-diagram d)
        ( htpy-eq-dependent-cocone-sequential-diagram d)

  extensionality-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    ( d ＝ d') ≃ htpy-dependent-cocone-sequential-diagram A P d d'
  pr1 (extensionality-dependent-cocone-sequential-diagram d d') =
    htpy-eq-dependent-cocone-sequential-diagram d d'
  pr2 (extensionality-dependent-cocone-sequential-diagram d d') =
    is-equiv-htpy-eq-dependent-cocone-sequential-diagram d d'

  eq-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram A c P) →
    htpy-dependent-cocone-sequential-diagram A P d d' → (d ＝ d')
  eq-htpy-dependent-cocone-sequential-diagram d d' =
    map-inv-equiv (extensionality-dependent-cocone-sequential-diagram d d')
```

### Dependent cocones under sequential diagrams on fiberwise constant type families are equivalent to regular cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) (Y : UU l3)
  where

  compute-dependent-cocone-constant-family-sequential-diagram :
    ( dependent-cocone-sequential-diagram A c (λ _ → Y)) ≃
    ( cocone-sequential-diagram A Y)
  compute-dependent-cocone-constant-family-sequential-diagram =
    equiv-tot
      ( λ i →
        equiv-Π-equiv-family
          ( λ n →
            equiv-Π-equiv-family
              ( λ a →
                equiv-concat
                  ( inv
                    ( tr-constant-type-family
                      ( coherence-triangle-cocone-sequential-diagram A c n a)
                      ( i n a)))
                  ( i (succ-ℕ n) (map-sequential-diagram A n a)))))

  map-compute-dependent-cocone-constant-family-sequential-diagram :
    dependent-cocone-sequential-diagram A c (λ _ → Y) →
    cocone-sequential-diagram A Y
  map-compute-dependent-cocone-constant-family-sequential-diagram =
    map-equiv compute-dependent-cocone-constant-family-sequential-diagram

  triangle-compute-dependent-cocone-constant-family-sequential-diagram :
    coherence-triangle-maps
      ( cocone-map-sequential-diagram A c)
      ( map-compute-dependent-cocone-constant-family-sequential-diagram)
      ( dependent-cocone-map-sequential-diagram A c (λ _ → Y))
  triangle-compute-dependent-cocone-constant-family-sequential-diagram h =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A c h)
      ( map-compute-dependent-cocone-constant-family-sequential-diagram
        ( dependent-cocone-map-sequential-diagram A c (λ _ → Y) h))
      ( ( ev-pair refl-htpy) ,
        ( λ n a →
          right-unit ∙
          left-transpose-eq-concat _ _ _
            ( inv
              ( apd-constant-type-family h
                ( coherence-triangle-cocone-sequential-diagram A c n a)))))
```

### Dependent cocones under sequential diagram are special cases of dependent coforks

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  module _
    { l3 : Level} (P : X → UU l3)
    where

    dependent-cofork-dependent-cocone-sequential-diagram :
      dependent-cocone-sequential-diagram A c P →
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P)
    pr1 (dependent-cofork-dependent-cocone-sequential-diagram d) =
      ind-Σ (map-dependent-cocone-sequential-diagram A P d)
    pr2 (dependent-cofork-dependent-cocone-sequential-diagram d) =
      ind-Σ (coherence-triangle-dependent-cocone-sequential-diagram A P d)

    dependent-cocone-dependent-cofork-sequential-diagram :
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P) →
      dependent-cocone-sequential-diagram A c P
    pr1 (dependent-cocone-dependent-cofork-sequential-diagram e) =
      ev-pair
        ( map-dependent-cofork
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A)
          ( P)
          ( e))
    pr2 (dependent-cocone-dependent-cofork-sequential-diagram e) =
      ev-pair
        ( coherence-dependent-cofork
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A)
          ( P)
          ( e))

    abstract
      is-section-dependent-cofork-dependent-cocone-sequential-diagram :
        ( dependent-cocone-dependent-cofork-sequential-diagram ∘
          dependent-cofork-dependent-cocone-sequential-diagram) ~
        ( id)
      is-section-dependent-cofork-dependent-cocone-sequential-diagram d =
        eq-htpy-dependent-cocone-sequential-diagram A P
          ( dependent-cocone-dependent-cofork-sequential-diagram
            ( dependent-cofork-dependent-cocone-sequential-diagram d))
          ( d)
          ( ev-pair refl-htpy , ev-pair right-unit-htpy)

      is-retraction-dependent-cofork-dependent-cocone-sequential-diagram :
        ( dependent-cofork-dependent-cocone-sequential-diagram ∘
          dependent-cocone-dependent-cofork-sequential-diagram) ~
        ( id)
      is-retraction-dependent-cofork-dependent-cocone-sequential-diagram e =
        eq-htpy-dependent-cofork
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A)
          ( P)
          ( dependent-cofork-dependent-cocone-sequential-diagram
            ( dependent-cocone-dependent-cofork-sequential-diagram e))
          ( e)
          ( refl-htpy , right-unit-htpy)

    is-equiv-dependent-cofork-dependent-cocone-sequential-diagram :
      is-equiv dependent-cofork-dependent-cocone-sequential-diagram
    is-equiv-dependent-cofork-dependent-cocone-sequential-diagram =
      is-equiv-is-invertible
        ( dependent-cocone-dependent-cofork-sequential-diagram)
        ( is-retraction-dependent-cofork-dependent-cocone-sequential-diagram)
        ( is-section-dependent-cofork-dependent-cocone-sequential-diagram)

    equiv-dependent-cofork-dependent-cocone-sequential-diagram :
      dependent-cocone-sequential-diagram A c P ≃
      dependent-cofork
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( P)
    pr1 equiv-dependent-cofork-dependent-cocone-sequential-diagram =
      dependent-cofork-dependent-cocone-sequential-diagram
    pr2 equiv-dependent-cofork-dependent-cocone-sequential-diagram =
      is-equiv-dependent-cofork-dependent-cocone-sequential-diagram

  triangle-dependent-cocone-dependent-cofork-sequential-diagram :
    { l3 : Level} (P : X → UU l3) →
    coherence-triangle-maps
      ( dependent-cocone-map-sequential-diagram A c P)
      ( dependent-cocone-dependent-cofork-sequential-diagram P)
      ( dependent-cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  triangle-dependent-cocone-dependent-cofork-sequential-diagram P h =
    eq-htpy-dependent-cocone-sequential-diagram A P
      ( dependent-cocone-map-sequential-diagram A c P h)
      ( dependent-cocone-dependent-cofork-sequential-diagram P
        ( dependent-cofork-map
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A)
          ( cofork-cocone-sequential-diagram A c)
          ( h)))
      ( ev-pair refl-htpy , ev-pair right-unit-htpy)
```
