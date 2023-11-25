# The dependent universal property of sequential colimits

```agda
module synthetic-homotopy-theory.dependent-universal-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **dependent universal property of sequential colimits**
is the statement that the dependent cocone postcomposition map

```text
dependent-cocone-map-sequential-diagram :
  ((x : X) → P x) → dependent-cocone-sequential-diagram P
```

is an [equivalence](foundation.equivalences.md).

## Definitions

### The dependent universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} (l : Level) (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit : UU (l1 ⊔ l2 ⊔ lsuc l)
  dependent-universal-property-sequential-colimit =
    ( P : X → UU l) → is-equiv (dependent-cocone-map-sequential-diagram A c P)
```

### The map induced by the dependent universal property of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {P : X → UU l3}
  ( dup-sequential-colimit :
    dependent-universal-property-sequential-colimit l3 A c)
  where

  map-dependent-universal-property-sequential-colimit :
    dependent-cocone-sequential-diagram A c P →
    ( x : X) → P x
  map-dependent-universal-property-sequential-colimit =
    map-inv-is-equiv (dup-sequential-colimit P)
```

## Properties

### The mediating map obtained by the dependent universal property is unique

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X) {P : X → UU l3}
  ( dup-sequential-colimit :
    dependent-universal-property-sequential-colimit l3 A c)
  ( d : dependent-cocone-sequential-diagram A c P)
  where

  htpy-dependent-cocone-dependent-universal-property-sequential-colimit :
    htpy-dependent-cocone-sequential-diagram A P
      ( dependent-cocone-map-sequential-diagram A c P
        ( map-dependent-universal-property-sequential-colimit A c
          ( dup-sequential-colimit)
          ( d)))
      ( d)
  htpy-dependent-cocone-dependent-universal-property-sequential-colimit =
    htpy-eq-dependent-cocone-sequential-diagram A P
      ( dependent-cocone-map-sequential-diagram A c P
        ( map-dependent-universal-property-sequential-colimit A c
          ( dup-sequential-colimit)
          ( d)))
      ( d)
      ( is-section-map-inv-is-equiv (dup-sequential-colimit P) d)

  abstract
    uniqueness-dependent-universal-property-sequential-colimit :
      is-contr
        ( Σ ( ( x : X) → P x)
            ( λ h →
              htpy-dependent-cocone-sequential-diagram A P
                ( dependent-cocone-map-sequential-diagram A c P h)
                ( d)))
    uniqueness-dependent-universal-property-sequential-colimit =
      is-contr-equiv'
        ( fiber (dependent-cocone-map-sequential-diagram A c P) d)
        ( equiv-tot
          ( λ h →
            extensionality-dependent-cocone-sequential-diagram A P
              ( dependent-cocone-map-sequential-diagram A c P h)
              ( d)))
        ( is-contr-map-is-equiv (dup-sequential-colimit P) d)
```

### Correspondence between dependent universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the dependent universal property of
sequential colimits if and only if the corresponding cofork has the dependent
universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer :
    ( {l : Level} →
      dependent-universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)) →
    ( {l : Level} →
      dependent-universal-property-sequential-colimit l A c)
  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
    ( dup-coequalizer)
    ( P) =
    is-equiv-left-map-triangle
      ( dependent-cocone-map-sequential-diagram A c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork A c P)
      ( dependent-cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
      ( triangle-dependent-cocone-sequential-diagram-dependent-cofork A c P)
      ( dup-coequalizer P)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-cofork A c P)

  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit :
    ( {l : Level} →
      dependent-universal-property-sequential-colimit l A c) →
    ( {l : Level} →
      dependent-universal-property-coequalizer l
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit
    ( dup-sequential-colimit)
    ( P) =
    is-equiv-top-map-triangle
      ( dependent-cocone-map-sequential-diagram A c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork A c P)
      ( dependent-cofork-map
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c))
      ( triangle-dependent-cocone-sequential-diagram-dependent-cofork A c P)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-cofork A c P)
      ( dup-sequential-colimit P)
```

### The non-dependent and dependent universal properties of sequential colimits are logically equivalent

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-dependent-universal-property-sequential-colimit :
    ( {l : Level} → dependent-universal-property-sequential-colimit l A c) →
    ( {l : Level} → universal-property-sequential-colimit l A c)
  universal-property-dependent-universal-property-sequential-colimit
    ( dup-sequential-colimit)
    ( Y) =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram A c)
      ( map-compute-dependent-cocone-sequential-diagram-constant-family A c Y)
      ( dependent-cocone-map-sequential-diagram A c (λ _ → Y))
      ( triangle-compute-dependent-cocone-sequential-diagram-constant-family A c
        ( Y))
      ( dup-sequential-colimit (λ _ → Y))
      ( is-equiv-map-equiv
        ( compute-dependent-cocone-sequential-diagram-constant-family A c Y))

  dependent-universal-property-universal-property-sequential-colimit :
    ( {l : Level} → universal-property-sequential-colimit l A c) →
    ( {l : Level} → dependent-universal-property-sequential-colimit l A c)
  dependent-universal-property-universal-property-sequential-colimit
    ( up-sequential-diagram) =
    dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
      ( A)
      ( c)
      ( dependent-universal-property-universal-property-coequalizer
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)
        ( cofork-cocone-sequential-diagram A c)
        ( universal-property-coequalizer-universal-property-sequential-colimit
          ( A)
          ( c)
          ( up-sequential-diagram)))
```
