# The dependent universal property of sequential colimits

```agda
module synthetic-homotopy-theory.dependent-universal-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
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
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit : UUω
  dependent-universal-property-sequential-colimit =
    {l : Level} (P : X → UU l) →
    is-equiv (dependent-cocone-map-sequential-diagram c P)
```

### The map induced by the dependent universal property of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {P : X → UU l3}
  ( dup-c :
    dependent-universal-property-sequential-colimit c)
  where

  equiv-dependent-universal-property-sequential-colimit :
    ((x : X) → P x) ≃ dependent-cocone-sequential-diagram c P
  pr1 equiv-dependent-universal-property-sequential-colimit =
    dependent-cocone-map-sequential-diagram c P
  pr2 equiv-dependent-universal-property-sequential-colimit = dup-c P

  map-dependent-universal-property-sequential-colimit :
    dependent-cocone-sequential-diagram c P →
    ( x : X) → P x
  map-dependent-universal-property-sequential-colimit =
    map-inv-is-equiv (dup-c P)
```

## Properties

### The mediating map obtained by the dependent universal property is unique

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {P : X → UU l3}
  ( dup-c :
    dependent-universal-property-sequential-colimit c)
  ( d : dependent-cocone-sequential-diagram c P)
  where

  htpy-dependent-cocone-dependent-universal-property-sequential-colimit :
    htpy-dependent-cocone-sequential-diagram P
      ( dependent-cocone-map-sequential-diagram c P
        ( map-dependent-universal-property-sequential-colimit
          ( dup-c)
          ( d)))
      ( d)
  htpy-dependent-cocone-dependent-universal-property-sequential-colimit =
    htpy-eq-dependent-cocone-sequential-diagram P
      ( dependent-cocone-map-sequential-diagram c P
        ( map-dependent-universal-property-sequential-colimit
          ( dup-c)
          ( d)))
      ( d)
      ( is-section-map-inv-is-equiv (dup-c P) d)

  abstract
    uniqueness-dependent-universal-property-sequential-colimit :
      is-contr
        ( Σ ( ( x : X) → P x)
            ( λ h →
              htpy-dependent-cocone-sequential-diagram P
                ( dependent-cocone-map-sequential-diagram c P h)
                ( d)))
    uniqueness-dependent-universal-property-sequential-colimit =
      is-contr-equiv'
        ( fiber (dependent-cocone-map-sequential-diagram c P) d)
        ( equiv-tot
          ( λ h →
            extensionality-dependent-cocone-sequential-diagram P
              ( dependent-cocone-map-sequential-diagram c P h)
              ( d)))
        ( is-contr-map-is-equiv (dup-c P) d)
```

### Correspondence between dependent universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the dependent universal property of
sequential colimits if and only if the corresponding cofork has the dependent
universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer :
    dependent-universal-property-coequalizer
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c) →
    dependent-universal-property-sequential-colimit c
  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
    ( dup-coequalizer)
    ( P) =
    is-equiv-left-map-triangle
      ( dependent-cocone-map-sequential-diagram c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dependent-cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dup-coequalizer P)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-cofork P)

  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit :
    dependent-universal-property-sequential-colimit c →
    dependent-universal-property-coequalizer
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c)
  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit
    ( dup-c)
    ( P) =
    is-equiv-top-map-triangle
      ( dependent-cocone-map-sequential-diagram c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dependent-cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-dependent-cocone-sequential-diagram-dependent-cofork P)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dup-c P)
```

### The nondependent and dependent universal properties of sequential colimits are logically equivalent

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  abstract
    universal-property-dependent-universal-property-sequential-colimit :
      dependent-universal-property-sequential-colimit c →
      universal-property-sequential-colimit c
    universal-property-dependent-universal-property-sequential-colimit
      ( dup-c)
      ( Y) =
      is-equiv-left-map-triangle
        ( cocone-map-sequential-diagram c)
        ( map-compute-dependent-cocone-sequential-diagram-constant-family Y)
        ( dependent-cocone-map-sequential-diagram c (λ _ → Y))
        ( triangle-compute-dependent-cocone-sequential-diagram-constant-family
          ( Y))
        ( dup-c (λ _ → Y))
        ( is-equiv-map-equiv
          ( compute-dependent-cocone-sequential-diagram-constant-family Y))

    dependent-universal-property-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      dependent-universal-property-sequential-colimit c
    dependent-universal-property-universal-property-sequential-colimit
      ( up-sequential-diagram) =
      dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
        ( c)
        ( dependent-universal-property-universal-property-coequalizer
          ( double-arrow-sequential-diagram A)
          ( cofork-cocone-sequential-diagram c)
          ( universal-property-coequalizer-universal-property-sequential-colimit
            ( c)
            ( up-sequential-diagram)))
```

### The 3-for-2 property of the dependent universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the dependent
universal property of sequential colimits, and a map between their vertices, we
prove that the other has the dependent universal property if and only if the map
is an [equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H : htpy-cocone-sequential-diagram (cocone-map-sequential-diagram c h) c')
  where

  abstract
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit :
      dependent-universal-property-sequential-colimit c →
      dependent-universal-property-sequential-colimit c' →
      is-equiv h
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit
      ( dup-c)
      ( dup-c') =
        is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
          ( c)
          ( c')
          ( h)
          ( H)
          ( universal-property-dependent-universal-property-sequential-colimit c
            ( dup-c))
          ( universal-property-dependent-universal-property-sequential-colimit
            ( c')
            ( dup-c'))

    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimit :
      dependent-universal-property-sequential-colimit c →
      is-equiv h →
      dependent-universal-property-sequential-colimit c'
    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimit
      ( dup-c) (is-equiv-h) =
      dependent-universal-property-universal-property-sequential-colimit c'
        ( universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
          ( c)
          ( c')
          ( h)
          ( H)
          ( universal-property-dependent-universal-property-sequential-colimit c
            ( dup-c))
          ( is-equiv-h))

    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      dependent-universal-property-sequential-colimit c' →
      dependent-universal-property-sequential-colimit c
    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equiv
      ( is-equiv-h)
      ( dup-c') =
      dependent-universal-property-universal-property-sequential-colimit c
        ( universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv
          ( c)
          ( c')
          ( h)
          ( H)
          ( is-equiv-h)
          ( universal-property-dependent-universal-property-sequential-colimit
            ( c')
            ( dup-c')))
```
