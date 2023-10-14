# Cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A **cocone under a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`** with vertex `X : 𝓤` consists of a family of maps `iₙ : A n → C` and
a family of [homotopies](foundation.homotopies.md) `Hₙ` asserting that the
triangles

```text
      aₙ
 A n ----> A (n + 1)
   \       /
    \     /
  iₙ \   / iₙ₊₁
      V V
       X
```

[commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### Cocones under sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (X : UU l2)
  where

  cocone-sequential-diagram : UU (l1 ⊔ l2)
  cocone-sequential-diagram =
    Σ ( ( n : ℕ) → family-sequential-diagram A n → X)
      ( λ i →
        ( n : ℕ) →
        coherence-triangle-maps
          ( i n)
          ( i (succ-ℕ n))
          ( map-sequential-diagram A n))
```

### Components of a cocone under a sequential diagram

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  injection-cocone-sequential-diagram :
    ( n : ℕ) → family-sequential-diagram A n → X
  injection-cocone-sequential-diagram = pr1 c

  coherence-triangle-cocone-sequential-diagram :
    ( n : ℕ) →
    coherence-triangle-maps
      ( injection-cocone-sequential-diagram n)
      ( injection-cocone-sequential-diagram (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-triangle-cocone-sequential-diagram = pr2 c
```

### Homotopies of cocones under a sequential diagram

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  where

  statement-coherence-htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) →
    ( (n : ℕ) →
      injection-cocone-sequential-diagram A c n ~
      injection-cocone-sequential-diagram A c' n) →
    UU (l1 ⊔ l2)
  statement-coherence-htpy-cocone-sequential-diagram c c' K =
    ( n : ℕ) →
      ( ( coherence-triangle-cocone-sequential-diagram A c n) ∙h
        ( K (succ-ℕ n) ·r map-sequential-diagram A n)) ~
      ( K n ∙h coherence-triangle-cocone-sequential-diagram A c' n)

  htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) → UU (l1 ⊔ l2)
  htpy-cocone-sequential-diagram c c' =
    Σ ( ( n : ℕ) →
        ( injection-cocone-sequential-diagram A c n) ~
        ( injection-cocone-sequential-diagram A c' n))
      ( statement-coherence-htpy-cocone-sequential-diagram c c')
```

### Components of a homotopy of cocones under a sequential diagram

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c c' : cocone-sequential-diagram A X)
  ( H : htpy-cocone-sequential-diagram A c c')
  where

  htpy-htpy-cocone-sequential-diagram :
    ( n : ℕ) →
    ( injection-cocone-sequential-diagram A c n) ~
    ( injection-cocone-sequential-diagram A c' n)
  htpy-htpy-cocone-sequential-diagram = pr1 H

  coherence-htpy-cocone-sequential-diagram :
    statement-coherence-htpy-cocone-sequential-diagram A c c'
      ( htpy-htpy-cocone-sequential-diagram)
  coherence-htpy-cocone-sequential-diagram = pr2 H
```

### Postcomposing cocones under a sequential diagram

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  cocone-map-sequential-diagram :
    { l : Level} {Y : UU l} →
    ( X → Y) → cocone-sequential-diagram A Y
  pr1 (cocone-map-sequential-diagram f) n =
    f ∘ injection-cocone-sequential-diagram A c n
  pr2 (cocone-map-sequential-diagram f) n =
    f ·l (coherence-triangle-cocone-sequential-diagram A c n)
```

## Properties

### Characterization of identity types of cocones under sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  where

  reflexive-htpy-cocone-sequential-diagram :
    ( c : cocone-sequential-diagram A X) → htpy-cocone-sequential-diagram A c c
  pr1 (reflexive-htpy-cocone-sequential-diagram c) n = refl-htpy
  pr2 (reflexive-htpy-cocone-sequential-diagram c) n = right-unit-htpy

  htpy-eq-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) → ( c ＝ c') →
    htpy-cocone-sequential-diagram A c c'
  htpy-eq-cocone-sequential-diagram c .c refl =
    reflexive-htpy-cocone-sequential-diagram c

  abstract
    is-torsorial-htpy-cocone-sequential-diagram :
      ( c : cocone-sequential-diagram A X) →
      is-contr
        ( Σ ( cocone-sequential-diagram A X)
            ( htpy-cocone-sequential-diagram A c))
    is-torsorial-htpy-cocone-sequential-diagram c =
      is-torsorial-Eq-structure
        ( ev-pair (statement-coherence-htpy-cocone-sequential-diagram A c))
        ( is-torsorial-binary-htpy (injection-cocone-sequential-diagram A c))
        ( ( injection-cocone-sequential-diagram A c) ,
          ( ev-pair refl-htpy))
        ( is-torsorial-binary-htpy
          ( λ n →
            ( coherence-triangle-cocone-sequential-diagram A c n) ∙h
            ( refl-htpy)))

    is-equiv-htpy-eq-cocone-sequential-diagram :
      ( c c' : cocone-sequential-diagram A X) →
      is-equiv (htpy-eq-cocone-sequential-diagram c c')
    is-equiv-htpy-eq-cocone-sequential-diagram c =
      fundamental-theorem-id
        ( is-torsorial-htpy-cocone-sequential-diagram c)
        ( htpy-eq-cocone-sequential-diagram c)

  eq-htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram A c c' →
    c ＝ c'
  eq-htpy-cocone-sequential-diagram c c' =
    map-inv-is-equiv (is-equiv-htpy-eq-cocone-sequential-diagram c c')
```

### Postcomposing a cocone under a sequential diagram by identity is the identity

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  cocone-map-id-sequential-diagram : cocone-map-sequential-diagram A c id ＝ c
  cocone-map-id-sequential-diagram =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A c id)
      ( c)
      ( ( ev-pair refl-htpy) ,
        ( λ n →
          ( right-unit-htpy) ∙h
          ( ap-id ∘ coherence-triangle-cocone-sequential-diagram A c n)))
```

### Postcomposing cocones under a sequential colimit distributes over function composition

```agda
module _
  { l1 l2 l3 l4 : Level} (A : sequential-diagram l1)
  { X : UU l2} {Y : UU l3} {Z : UU l4}
  ( c : cocone-sequential-diagram A X)
  where

  cocone-map-comp-sequential-diagram :
    ( h : X → Y) (k : Y → Z) →
    cocone-map-sequential-diagram A c (k ∘ h) ＝
    cocone-map-sequential-diagram A (cocone-map-sequential-diagram A c h) k
  cocone-map-comp-sequential-diagram h k =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A c (k ∘ h))
      ( cocone-map-sequential-diagram A (cocone-map-sequential-diagram A c h) k)
      ( ( ev-pair refl-htpy) ,
        ( λ n →
          ( right-unit-htpy) ∙h
          ( ap-comp k h ∘ coherence-triangle-cocone-sequential-diagram A c n)))
```

### Cocones under sequential diagrams are a special case of coequalizers

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  bottom-map-cofork-cocone-sequential-diagram :
    Σ ℕ (family-sequential-diagram A) → Σ ℕ (family-sequential-diagram A)
  bottom-map-cofork-cocone-sequential-diagram = id

  top-map-cofork-cocone-sequential-diagram :
    Σ ℕ (family-sequential-diagram A) → Σ ℕ (family-sequential-diagram A)
  top-map-cofork-cocone-sequential-diagram =
    map-Σ
      ( family-sequential-diagram A)
      ( succ-ℕ)
      ( map-sequential-diagram A)

  module _
    { l2 : Level} {X : UU l2}
    where

    cofork-cocone-sequential-diagram :
      cocone-sequential-diagram A X →
      cofork
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( X)
    pr1 (cofork-cocone-sequential-diagram c) =
      ind-Σ (injection-cocone-sequential-diagram A c)
    pr2 (cofork-cocone-sequential-diagram c) =
      ind-Σ (coherence-triangle-cocone-sequential-diagram A c)

    cocone-sequential-diagram-cofork :
      cofork
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( X) →
      cocone-sequential-diagram A X
    pr1 (cocone-sequential-diagram-cofork e) =
      ev-pair
        ( map-cofork
          ( bottom-map-cofork-cocone-sequential-diagram)
          ( top-map-cofork-cocone-sequential-diagram)
          ( e))
    pr2 (cocone-sequential-diagram-cofork e) =
      ev-pair
        ( coherence-cofork
          ( bottom-map-cofork-cocone-sequential-diagram)
          ( top-map-cofork-cocone-sequential-diagram)
          ( e))

    abstract
      is-section-cofork-cocone-sequential-diagram :
        cocone-sequential-diagram-cofork ∘ cofork-cocone-sequential-diagram ~ id
      is-section-cofork-cocone-sequential-diagram c =
        eq-htpy-cocone-sequential-diagram A
          ( cocone-sequential-diagram-cofork
            ( cofork-cocone-sequential-diagram c))
          ( c)
          ( ev-pair refl-htpy ,
            ev-pair right-unit-htpy)

      is-retraction-cofork-cocone-sequential-diagram :
        cofork-cocone-sequential-diagram ∘ cocone-sequential-diagram-cofork ~ id
      is-retraction-cofork-cocone-sequential-diagram e =
        eq-htpy-cofork
          ( bottom-map-cofork-cocone-sequential-diagram)
          ( top-map-cofork-cocone-sequential-diagram)
          ( cofork-cocone-sequential-diagram
            ( cocone-sequential-diagram-cofork e))
          ( e)
          ( refl-htpy , right-unit-htpy)

    is-equiv-cofork-cocone-sequential-diagram :
      is-equiv cofork-cocone-sequential-diagram
    is-equiv-cofork-cocone-sequential-diagram =
      is-equiv-is-invertible
        ( cocone-sequential-diagram-cofork)
        ( is-retraction-cofork-cocone-sequential-diagram)
        ( is-section-cofork-cocone-sequential-diagram)

    equiv-cofork-cocone-sequential-diagram :
      cocone-sequential-diagram A X ≃
      cofork
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( X)
    pr1 equiv-cofork-cocone-sequential-diagram =
      cofork-cocone-sequential-diagram
    pr2 equiv-cofork-cocone-sequential-diagram =
      is-equiv-cofork-cocone-sequential-diagram

  triangle-cocone-sequential-diagram-cofork :
    { l2 l3 : Level} {X : UU l2} {Y : UU l3} →
    ( c : cocone-sequential-diagram A X) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram A c {Y = Y})
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( cofork-cocone-sequential-diagram c))
  triangle-cocone-sequential-diagram-cofork c h =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A c h)
      ( cocone-sequential-diagram-cofork
        ( cofork-map
          ( bottom-map-cofork-cocone-sequential-diagram)
          ( top-map-cofork-cocone-sequential-diagram)
          ( cofork-cocone-sequential-diagram c)
          ( h)))
      ( ev-pair refl-htpy ,
        ev-pair right-unit-htpy)
```

## References

1. Kristina Sojakova, Floris van Doorn, and Egbert Rijke. 2020. Sequential
   Colimits in Homotopy Type Theory. In Proceedings of the 35th Annual ACM/IEEE
   Symposium on Logic in Computer Science (LICS '20). Association for Computing
   Machinery, New York, NY, USA, 845–858,
   [DOI:10.1145](https://doi.org/10.1145/3373718.3394801)
