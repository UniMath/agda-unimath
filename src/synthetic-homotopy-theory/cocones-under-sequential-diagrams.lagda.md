# Cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A **cocone under a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`** with codomain `X : 𝓤` consists of a family of maps `iₙ : A n → C` and
a family of [homotopies](foundation.homotopies.md) `Hₙ` asserting that the
triangles

```text
       aₙ
 Aₙ ------> Aₙ₊₁
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

### Components of cocones under sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  map-cocone-sequential-diagram : (n : ℕ) → family-sequential-diagram A n → X
  map-cocone-sequential-diagram = pr1 c

  coherence-triangle-cocone-sequential-diagram :
    ( n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-sequential-diagram n)
      ( map-cocone-sequential-diagram (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-triangle-cocone-sequential-diagram = pr2 c
```

### Homotopies of cocones under a sequential diagram

A **homotopy** between two cocones `(X, i, H)` and `(X, j, L)` with the same
vertex consists of a [sequence](foundation.dependent-sequences.md) of
[homotopies](foundation.homotopies.md) `Kₙ : iₙ ~ jₙ` and a coherence datum
filling the "pinched cylinder" with the faces `Kₙ`, `Hₙ`, `Lₙ` and `Kₙ₊₁`.

The coherence datum may be better understood by viewing a cocone as a
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) from
`(A, a)` to the constant cocone `(n ↦ X, n ↦ id)`. Then a homotopy of cocones is
a regular homotopy of morphisms of sequential diagrams.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  where

  coherence-htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) →
    ( (n : ℕ) →
      map-cocone-sequential-diagram A c n ~
      map-cocone-sequential-diagram A c' n) →
    UU (l1 ⊔ l2)
  coherence-htpy-cocone-sequential-diagram c c' K =
    ( n : ℕ) →
    coherence-square-homotopies
      ( K n)
      ( coherence-triangle-cocone-sequential-diagram A c n)
      ( coherence-triangle-cocone-sequential-diagram A c' n)
      ( K (succ-ℕ n) ·r map-sequential-diagram A n)

  htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) → UU (l1 ⊔ l2)
  htpy-cocone-sequential-diagram c c' =
    Σ ( ( n : ℕ) →
        ( map-cocone-sequential-diagram A c n) ~
        ( map-cocone-sequential-diagram A c' n))
      ( coherence-htpy-cocone-sequential-diagram c c')
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
    ( map-cocone-sequential-diagram A c n) ~
    ( map-cocone-sequential-diagram A c' n)
  htpy-htpy-cocone-sequential-diagram = pr1 H

  coherence-htpy-htpy-cocone-sequential-diagram :
    coherence-htpy-cocone-sequential-diagram A c c'
      ( htpy-htpy-cocone-sequential-diagram)
  coherence-htpy-htpy-cocone-sequential-diagram = pr2 H
```

### Postcomposing cocones under a sequential diagram with a map

Given a cocone `c` with vertex `X` under `(A, a)` and a map `f : X → Y`, we may
extend `c` to a cocone with vertex `Y`.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  cocone-map-sequential-diagram :
    { l : Level} {Y : UU l} →
    ( X → Y) → cocone-sequential-diagram A Y
  pr1 (cocone-map-sequential-diagram f) n =
    f ∘ map-cocone-sequential-diagram A c n
  pr2 (cocone-map-sequential-diagram f) n =
    f ·l (coherence-triangle-cocone-sequential-diagram A c n)
```

### Postcomposition cocones under postcomposition sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (X : UU l1) (A : sequential-diagram l2) {Y : UU l3}
  ( c : cocone-sequential-diagram A Y)
  where

  cocone-postcomp-sequential-diagram :
    cocone-sequential-diagram (postcomp-sequential-diagram X A) (X → Y)
  pr1 cocone-postcomp-sequential-diagram n g x =
    map-cocone-sequential-diagram A c n (g x)
  pr2 cocone-postcomp-sequential-diagram n g =
    eq-htpy (λ x → coherence-triangle-cocone-sequential-diagram A c n (g x))
```

## Properties

### Characterization of identity types of cocones under sequential diagrams

[Equality](foundation.identity-types.md) of cocones with the same vertex is
captured by a homotopy between them.

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
      is-torsorial (htpy-cocone-sequential-diagram A c)
    is-torsorial-htpy-cocone-sequential-diagram c =
      is-torsorial-Eq-structure
        ( ev-pair (coherence-htpy-cocone-sequential-diagram A c))
        ( is-torsorial-binary-htpy (map-cocone-sequential-diagram A c))
        ( ( map-cocone-sequential-diagram A c) ,
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

  extensionality-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) →
    (c ＝ c') ≃ htpy-cocone-sequential-diagram A c c'
  pr1 (extensionality-cocone-sequential-diagram c c') =
    htpy-eq-cocone-sequential-diagram c c'
  pr2 (extensionality-cocone-sequential-diagram c c') =
    is-equiv-htpy-eq-cocone-sequential-diagram c c'

  eq-htpy-cocone-sequential-diagram :
    ( c c' : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram A c c' →
    c ＝ c'
  eq-htpy-cocone-sequential-diagram c c' =
    map-inv-equiv (extensionality-cocone-sequential-diagram c c')
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

In other words, extending a cocone `c` with vertex `X` by the map
`k ∘ h : X → Z` results in the same cocone as first extending by `h` and then by
`k`.

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

The data of a cocone

```text
       aₙ
 Aₙ ------> Aₙ₊₁
   \  Hₙ   /
    \ =>  /
  iₙ \   / iₙ₊₁
      V V
       X
```

can be [uncurried](foundation.dependent-pair-types.md) to get the equivalent
diagram comprising of the single triangle

```text
         tot₊₁ a
 (Σ ℕ A) ------> (Σ ℕ A)
        \       /
         \     /
       i  \   /  i
           V V
            X
```

which is exactly a cofork of the identity map and `tot₊₁ a`.

Under this mapping
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
correspond to
[coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md),
which is formalized in
[universal-property-sequential-colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

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

    cofork-cocone-sequential-diagram :
      cocone-sequential-diagram A X →
      cofork
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( X)
    pr1 (cofork-cocone-sequential-diagram c) =
      ind-Σ (map-cocone-sequential-diagram A c)
    pr2 (cofork-cocone-sequential-diagram c) =
      ind-Σ (coherence-triangle-cocone-sequential-diagram A c)

    abstract
      is-section-cocone-sequential-diagram-cofork :
        cofork-cocone-sequential-diagram ∘ cocone-sequential-diagram-cofork ~ id
      is-section-cocone-sequential-diagram-cofork e =
        eq-htpy-cofork
          ( bottom-map-cofork-cocone-sequential-diagram)
          ( top-map-cofork-cocone-sequential-diagram)
          ( cofork-cocone-sequential-diagram
            ( cocone-sequential-diagram-cofork e))
          ( e)
          ( refl-htpy , right-unit-htpy)

      is-retraction-cocone-sequential-diagram-cofork :
        cocone-sequential-diagram-cofork ∘ cofork-cocone-sequential-diagram ~ id
      is-retraction-cocone-sequential-diagram-cofork c =
        eq-htpy-cocone-sequential-diagram A
          ( cocone-sequential-diagram-cofork
            ( cofork-cocone-sequential-diagram c))
          ( c)
          ( ev-pair refl-htpy ,
            ev-pair right-unit-htpy)

    is-equiv-cocone-sequential-diagram-cofork :
      is-equiv cocone-sequential-diagram-cofork
    is-equiv-cocone-sequential-diagram-cofork =
      is-equiv-is-invertible
        ( cofork-cocone-sequential-diagram)
        ( is-retraction-cocone-sequential-diagram-cofork)
        ( is-section-cocone-sequential-diagram-cofork)

    equiv-cocone-sequential-diagram-cofork :
      cofork
        ( bottom-map-cofork-cocone-sequential-diagram)
        ( top-map-cofork-cocone-sequential-diagram)
        ( X) ≃
      cocone-sequential-diagram A X
    pr1 equiv-cocone-sequential-diagram-cofork =
      cocone-sequential-diagram-cofork
    pr2 equiv-cocone-sequential-diagram-cofork =
      is-equiv-cocone-sequential-diagram-cofork

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
