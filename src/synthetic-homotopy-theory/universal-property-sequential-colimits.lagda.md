# The universal property of sequential colimits

```agda
module synthetic-homotopy-theory.universal-property-sequential-colimits where
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
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **universal property of sequential colimits** is the
statement that the cocone postcomposition map

```text
cocone-map-sequential-diagram : (X → Y) → cocone-sequential-diagram Y
```

is an [equivalence](foundation.equivalences.md).

A sequential colimit `X` may be visualized as a "point in infinity" in the
diagram

```text
     a₀      a₁      a₂     i
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X.
```

## Definitions

### The universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit : UUω
  universal-property-sequential-colimit =
    {l : Level} → (Y : UU l) →
    is-equiv (cocone-map-sequential-diagram c {Y = Y})
```

### The map induced by the universal property of sequential colimits

The universal property allows us to construct a map from the colimit by
providing a cocone under the sequential diagram.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  where

  equiv-universal-property-sequential-colimit :
    (X → Y) ≃ cocone-sequential-diagram A Y
  pr1 equiv-universal-property-sequential-colimit =
    cocone-map-sequential-diagram c
  pr2 equiv-universal-property-sequential-colimit =
    up-sequential-colimit Y

  map-universal-property-sequential-colimit :
    cocone-sequential-diagram A Y → (X → Y)
  map-universal-property-sequential-colimit =
    map-inv-is-equiv (up-sequential-colimit Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  ( c' : cocone-sequential-diagram A Y)
  where

  htpy-cocone-universal-property-sequential-colimit :
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
  htpy-cocone-universal-property-sequential-colimit =
    htpy-eq-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
      ( is-section-map-inv-is-equiv (up-sequential-colimit Y) c')

  abstract
    uniqueness-map-universal-property-sequential-colimit :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c h)
                ( c')))
    uniqueness-map-universal-property-sequential-colimit =
      is-contr-equiv'
        ( fiber (cocone-map-sequential-diagram c) c')
        ( equiv-tot
          ( λ h →
            extensionality-cocone-sequential-diagram A
              ( cocone-map-sequential-diagram c h)
              ( c')))
        ( is-contr-map-is-equiv (up-sequential-colimit Y) c')
```

### Correspondence between universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the universal property of sequential
colimits if and only if the
[corresponding cofork](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
has the universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit-universal-property-coequalizer :
    ( {l : Level} →
      universal-property-coequalizer l
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c)) →
    universal-property-sequential-colimit c
  universal-property-sequential-colimit-universal-property-coequalizer
    ( up-cofork)
    ( Y) =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-cocone-sequential-diagram-cofork c)
      ( up-cofork Y)
      ( is-equiv-cocone-sequential-diagram-cofork)

  universal-property-coequalizer-universal-property-sequential-colimit :
    universal-property-sequential-colimit c →
    ( {l : Level} →
      universal-property-coequalizer l
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
  universal-property-coequalizer-universal-property-sequential-colimit
    ( up-sequential-colimit)
    ( Y) =
    is-equiv-top-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-cocone-sequential-diagram-cofork c)
      ( is-equiv-cocone-sequential-diagram-cofork)
      ( up-sequential-colimit Y)
```

### The universal property of colimits is preserved by equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} {c : cocone-sequential-diagram A X}
  {B : sequential-diagram l3} {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (e : equiv-sequential-diagram A B)
  (e' : equiv-cocone-equiv-sequential-diagram c c' e)
  where

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram :
    universal-property-sequential-colimit c' →
    universal-property-sequential-colimit c
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram
    up-c' =
    universal-property-sequential-colimit-universal-property-coequalizer c
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow
        ( cofork-cocone-sequential-diagram c)
        ( cofork-cocone-sequential-diagram c')
        ( equiv-double-arrow-equiv-sequential-diagram A B e)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagram c c' e e')
        ( universal-property-coequalizer-universal-property-sequential-colimit _
          ( up-c')))

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram' :
    universal-property-sequential-colimit c →
    universal-property-sequential-colimit c'
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram'
    up-c =
    universal-property-sequential-colimit-universal-property-coequalizer c'
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow'
        ( cofork-cocone-sequential-diagram c)
        ( cofork-cocone-sequential-diagram c')
        ( equiv-double-arrow-equiv-sequential-diagram A B e)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagram c c' e e')
        ( universal-property-coequalizer-universal-property-sequential-colimit _
          ( up-c)))
```

### The 3-for-2 property of the universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the universal
property of sequential colimits, and a map between their vertices, we prove that
the other has the universal property if and only if the map is an
[equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H :
    htpy-cocone-sequential-diagram (cocone-map-sequential-diagram c h) c')
  where

  inv-triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps'
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  inv-triangle-cocone-map-precomp-sequential-diagram Z k =
    ( cocone-map-comp-sequential-diagram A c h k) ∙
    ( ap
      ( λ d → cocone-map-sequential-diagram d k)
      ( eq-htpy-cocone-sequential-diagram A
        ( cocone-map-sequential-diagram c h)
        ( c')
        ( H)))

  triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  triangle-cocone-map-precomp-sequential-diagram Z =
    inv-htpy (inv-triangle-cocone-map-precomp-sequential-diagram Z)

  abstract
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      universal-property-sequential-colimit c' →
      is-equiv h
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( up-sequential-colimit') =
      is-equiv-is-equiv-precomp h
        ( λ Z →
          is-equiv-top-map-triangle
            ( cocone-map-sequential-diagram c')
            ( cocone-map-sequential-diagram c)
            ( precomp h Z)
            ( triangle-cocone-map-precomp-sequential-diagram Z)
            ( up-sequential-colimit Z)
            ( up-sequential-colimit' Z))

    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      is-equiv h →
      universal-property-sequential-colimit c'
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( is-equiv-h)
      ( Z) =
      is-equiv-left-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
        ( up-sequential-colimit Z)

    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      universal-property-sequential-colimit c' →
      universal-property-sequential-colimit c
    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv
      ( is-equiv-h)
      ( up-sequential-colimit)
      ( Z) =
      is-equiv-right-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( up-sequential-colimit Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Unique uniqueness of of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  { c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { c' : cocone-sequential-diagram A Y}
  ( up-c' : universal-property-sequential-colimit c')
  where

  abstract
    uniquely-unique-sequential-colimit :
      is-contr
        ( Σ ( X ≃ Y)
            ( λ e →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c (map-equiv e))
                ( c')))
    uniquely-unique-sequential-colimit =
      is-torsorial-Eq-subtype
        ( uniqueness-map-universal-property-sequential-colimit up-c c')
        ( is-property-is-equiv)
        ( map-universal-property-sequential-colimit up-c c')
        ( htpy-cocone-universal-property-sequential-colimit up-c c')
        ( is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
          ( c)
          ( c')
          ( map-universal-property-sequential-colimit up-c c')
          ( htpy-cocone-universal-property-sequential-colimit up-c c')
          ( up-c)
          ( up-c'))
```
