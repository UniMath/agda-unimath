# Dependent cocones under sequential diagrams

```agda
{-# OPTIONS --allow-unsolved-metas #-}
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
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) `c`
with vertex `X` under it, and a type family `P : X → 𝒰`, we may construct
_dependent_ cocones on `P` over `c`.

A **dependent cocone under a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)** on `P`
over `c ≐ (X, i, H)` consists of a [sequence](foundation.dependent-sequences.md)
of dependent maps `i'ₙ : (x : Aₙ) → P (iₙ x)` and a sequence of
[dependent homotopies](foundation.dependent-homotopies.md)
`H'ₙ : i'ₙ ~ i'ₙ₊₁ ∘ aₙ` over `H`.

## Definitions

### Dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X) (P : X → UU l3)
  where

  dependent-cocone-sequential-diagram : UU (l1 ⊔ l3)
  dependent-cocone-sequential-diagram =
    Σ ( ( n : ℕ) (a : family-sequential-diagram A n) →
        P (map-cocone-sequential-diagram c n a))
      ( λ i →
        ( n : ℕ) →
        dependent-homotopy (λ _ → P)
          ( coherence-cocone-sequential-diagram c n)
          ( i n)
          ( i (succ-ℕ n) ∘ map-sequential-diagram A n))
```

### Components of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  ( d : dependent-cocone-sequential-diagram c P)
  where

  map-dependent-cocone-sequential-diagram :
    ( n : ℕ) (a : family-sequential-diagram A n) →
    P (map-cocone-sequential-diagram c n a)
  map-dependent-cocone-sequential-diagram = pr1 d

  coherence-triangle-dependent-cocone-sequential-diagram :
    ( n : ℕ) → (a : family-sequential-diagram A n) →
    dependent-identification P
      ( coherence-cocone-sequential-diagram c n a)
      ( map-dependent-cocone-sequential-diagram n a)
      ( map-dependent-cocone-sequential-diagram
        ( succ-ℕ n)
        ( map-sequential-diagram A n a))
  coherence-triangle-dependent-cocone-sequential-diagram = pr2 d
```

### Homotopies of dependent cocones under sequential diagrams

A **homotopy** of dependent cocones `(P, i', H')` and `(P, j', L')` consists of
a sequence of [homotopies](foundation.homotopies.md) `Kₙ : i'ₙ ~ j'ₙ` and a
coherence datum.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  coherence-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram c P) →
    ( K :
      ( n : ℕ) →
      ( map-dependent-cocone-sequential-diagram P d n) ~
      ( map-dependent-cocone-sequential-diagram P d' n)) →
    UU (l1 ⊔ l3)
  coherence-htpy-dependent-cocone-sequential-diagram d d' K =
    ( n : ℕ) (a : family-sequential-diagram A n) →
    ( ( coherence-triangle-dependent-cocone-sequential-diagram P d n a) ∙
      ( K (succ-ℕ n) (map-sequential-diagram A n a))) ＝
    ( ( ap
        ( tr P (coherence-cocone-sequential-diagram c n a))
        ( K n a)) ∙
      ( coherence-triangle-dependent-cocone-sequential-diagram P d' n a))

  htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram c P) →
    UU (l1 ⊔ l3)
  htpy-dependent-cocone-sequential-diagram d d' =
    Σ ( ( n : ℕ) →
        ( map-dependent-cocone-sequential-diagram P d n) ~
        ( map-dependent-cocone-sequential-diagram P d' n))
      ( coherence-htpy-dependent-cocone-sequential-diagram d d')
```

### Components of homotopies of dependent cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  { d d' : dependent-cocone-sequential-diagram c P}
  ( H : htpy-dependent-cocone-sequential-diagram P d d')
  where

  htpy-htpy-dependent-cocone-sequential-diagram :
    ( n : ℕ) →
    ( map-dependent-cocone-sequential-diagram P d n) ~
    ( map-dependent-cocone-sequential-diagram P d' n)
  htpy-htpy-dependent-cocone-sequential-diagram = pr1 H

  coherence-htpy-htpy-dependent-cocone-sequential-diagram :
    coherence-htpy-dependent-cocone-sequential-diagram P d d'
      ( htpy-htpy-dependent-cocone-sequential-diagram)
  coherence-htpy-htpy-dependent-cocone-sequential-diagram = pr2 H
```

### Inversion of homotopies of dependent cocones under sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X} (P : X → UU l3)
  {d d' : dependent-cocone-sequential-diagram c P}
  (H : htpy-dependent-cocone-sequential-diagram P d d')
  where

  inv-htpy-dependent-cocone-sequential-diagram :
    htpy-dependent-cocone-sequential-diagram P d' d
  inv-htpy-dependent-cocone-sequential-diagram = ?
```

### Concatenation of homotopies of dependent cocones under sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X} (P : X → UU l3)
  {d d' d'' : dependent-cocone-sequential-diagram c P}
  (H : htpy-dependent-cocone-sequential-diagram P d d')
  (K : htpy-dependent-cocone-sequential-diagram P d' d'')
  where

  concat-htpy-dependent-cocone-sequential-diagram :
    htpy-dependent-cocone-sequential-diagram P d d''
  concat-htpy-dependent-cocone-sequential-diagram = {!!}
```

### Obtaining dependent cocones under sequential diagrams by postcomposing cocones under sequential diagrams with dependent maps

Given a cocone `c` with vertex `X`, and a dependent map `h : (x : X) → P x`, we
may extend `c` to a dependent cocone on `P` over `c`.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-cocone-map-sequential-diagram :
    { l : Level} (P : X → UU l) →
    ( (x : X) → P x) → dependent-cocone-sequential-diagram c P
  pr1 (dependent-cocone-map-sequential-diagram P h) n =
    h ∘ map-cocone-sequential-diagram c n
  pr2 (dependent-cocone-map-sequential-diagram P h) n =
    apd h ∘ coherence-cocone-sequential-diagram c n
```

## Properties

### Characterization of identity types of dependent cocones under sequential diagrams

[Equality](foundation.identity-types.md) of dependent cocones is captured by a
homotopy between them.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} (P : X → UU l3)
  where

  refl-htpy-dependent-cocone-sequential-diagram :
    ( d : dependent-cocone-sequential-diagram c P) →
    htpy-dependent-cocone-sequential-diagram P d d
  pr1 (refl-htpy-dependent-cocone-sequential-diagram d) n = refl-htpy
  pr2 (refl-htpy-dependent-cocone-sequential-diagram d) n = right-unit-htpy

  htpy-eq-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram c P) →
    ( d ＝ d') → htpy-dependent-cocone-sequential-diagram P d d'
  htpy-eq-dependent-cocone-sequential-diagram d .d refl =
    refl-htpy-dependent-cocone-sequential-diagram d

  abstract
    is-torsorial-htpy-dependent-cocone-sequential-diagram :
      ( d : dependent-cocone-sequential-diagram c P) →
      is-torsorial (htpy-dependent-cocone-sequential-diagram P d)
    is-torsorial-htpy-dependent-cocone-sequential-diagram d =
      is-torsorial-Eq-structure
        ( is-torsorial-binary-htpy
          ( map-dependent-cocone-sequential-diagram P d))
        ( map-dependent-cocone-sequential-diagram P d ,
          ev-pair refl-htpy)
        ( is-torsorial-binary-htpy
          ( λ n →
            ( coherence-triangle-dependent-cocone-sequential-diagram P d n) ∙h
            ( refl-htpy)))

    is-equiv-htpy-eq-dependent-cocone-sequential-diagram :
      ( d d' : dependent-cocone-sequential-diagram c P) →
      is-equiv (htpy-eq-dependent-cocone-sequential-diagram d d')
    is-equiv-htpy-eq-dependent-cocone-sequential-diagram d =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cocone-sequential-diagram d)
        ( htpy-eq-dependent-cocone-sequential-diagram d)

  extensionality-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram c P) →
    ( d ＝ d') ≃ htpy-dependent-cocone-sequential-diagram P d d'
  pr1 (extensionality-dependent-cocone-sequential-diagram d d') =
    htpy-eq-dependent-cocone-sequential-diagram d d'
  pr2 (extensionality-dependent-cocone-sequential-diagram d d') =
    is-equiv-htpy-eq-dependent-cocone-sequential-diagram d d'

  eq-htpy-dependent-cocone-sequential-diagram :
    ( d d' : dependent-cocone-sequential-diagram c P) →
    htpy-dependent-cocone-sequential-diagram P d d' → (d ＝ d')
  eq-htpy-dependent-cocone-sequential-diagram d d' =
    map-inv-equiv (extensionality-dependent-cocone-sequential-diagram d d')
```

### Dependent cocones under sequential diagrams on fiberwise constant type families are equivalent to regular cocones under sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} (Y : UU l3)
  where

  compute-dependent-cocone-sequential-diagram-constant-family :
    ( dependent-cocone-sequential-diagram c (λ _ → Y)) ≃
    ( cocone-sequential-diagram A Y)
  compute-dependent-cocone-sequential-diagram-constant-family =
    equiv-tot
      ( λ i →
        equiv-Π-equiv-family
          ( λ n →
            equiv-Π-equiv-family
              ( λ a →
                equiv-concat
                  ( inv
                    ( tr-constant-type-family
                      ( coherence-cocone-sequential-diagram c n a)
                      ( i n a)))
                  ( i (succ-ℕ n) (map-sequential-diagram A n a)))))

  map-compute-dependent-cocone-sequential-diagram-constant-family :
    dependent-cocone-sequential-diagram c (λ _ → Y) →
    cocone-sequential-diagram A Y
  map-compute-dependent-cocone-sequential-diagram-constant-family =
    map-equiv compute-dependent-cocone-sequential-diagram-constant-family

  triangle-compute-dependent-cocone-sequential-diagram-constant-family :
    coherence-triangle-maps
      ( cocone-map-sequential-diagram c)
      ( map-compute-dependent-cocone-sequential-diagram-constant-family)
      ( dependent-cocone-map-sequential-diagram c (λ _ → Y))
  triangle-compute-dependent-cocone-sequential-diagram-constant-family h =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c h)
      ( map-compute-dependent-cocone-sequential-diagram-constant-family
        ( dependent-cocone-map-sequential-diagram c (λ _ → Y) h))
      ( ( ev-pair refl-htpy) ,
        ( λ n a →
          right-unit ∙
          left-transpose-eq-concat _ _ _
            ( inv
              ( apd-constant-type-family h
                ( coherence-cocone-sequential-diagram c n a)))))
```
