# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.fibers-of-maps
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Given a [double arrow](foundation.double-arrows.md) `f, g : A → B`, consider a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex `X`. The
**universal property of coequalizers** is the statement that the cofork
postcomposition map

```text
cofork-map : (X → Y) → cofork Y
```

is an [equivalence](foundation.equivalences.md).

## Definitions

### The universal property of coequalizers

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  universal-property-coequalizer : UUω
  universal-property-coequalizer =
    {l : Level} (Y : UU l) → is-equiv (cofork-map a e {Y = Y})

module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X) {Y : UU l4}
  (up-coequalizer : universal-property-coequalizer a e)
  where

  map-universal-property-coequalizer : cofork a Y → (X → Y)
  map-universal-property-coequalizer = map-inv-is-equiv (up-coequalizer Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X) {Y : UU l4}
  (up-coequalizer : universal-property-coequalizer a e)
  (e' : cofork a Y)
  where

  htpy-cofork-map-universal-property-coequalizer :
    htpy-cofork a
      ( cofork-map a e
        ( map-universal-property-coequalizer a e up-coequalizer e'))
      ( e')
  htpy-cofork-map-universal-property-coequalizer =
    htpy-cofork-eq a
      ( cofork-map a e
        ( map-universal-property-coequalizer a e up-coequalizer e'))
      ( e')
      ( is-section-map-inv-is-equiv (up-coequalizer Y) e')

  abstract
    uniqueness-map-universal-property-coequalizer :
      is-contr (Σ (X → Y) (λ h → htpy-cofork a (cofork-map a e h) e'))
    uniqueness-map-universal-property-coequalizer =
      is-contr-is-equiv'
        ( fiber (cofork-map a e) e')
        ( tot (λ h → htpy-cofork-eq a (cofork-map a e h) e'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h → is-equiv-htpy-cofork-eq a (cofork-map a e h) e'))
        ( is-contr-map-is-equiv (up-coequalizer Y) e')
```

### A cofork has the universal property of coequalizers if and only if the corresponding cocone has the universal property of pushouts

As mentioned in [`coforks`](synthetic-homotopy-theory.coforks.md), coforks can
be thought of as special cases of cocones under spans. This theorem makes it
more precise, asserting that under this mapping,
[coequalizers](synthetic-homotopy-theory.coequalizers.md) correspond to
[pushouts](synthetic-homotopy-theory.pushouts.md).

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  universal-property-coequalizer-universal-property-pushout :
    universal-property-pushout
      ( vertical-map-span-cocone-cofork a)
      ( horizontal-map-span-cocone-cofork a)
      ( cocone-codiagonal-cofork a e) →
      universal-property-coequalizer a e
  universal-property-coequalizer-universal-property-pushout up-pushout Y =
    is-equiv-left-map-triangle
      ( cofork-map a e)
      ( cofork-cocone-codiagonal a)
      ( cocone-map
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e))
      ( triangle-cofork-cocone a e)
      ( up-pushout Y)
      ( is-equiv-cofork-cocone-codiagonal a)

  universal-property-pushout-universal-property-coequalizer :
    universal-property-coequalizer a e →
    universal-property-pushout
      ( vertical-map-span-cocone-cofork a)
      ( horizontal-map-span-cocone-cofork a)
      ( cocone-codiagonal-cofork a e)
  universal-property-pushout-universal-property-coequalizer up-coequalizer Y =
    is-equiv-top-map-triangle
      ( cofork-map a e)
      ( cofork-cocone-codiagonal a)
      ( cocone-map
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e))
      ( triangle-cofork-cocone a e)
      ( is-equiv-cofork-cocone-codiagonal a)
      ( up-coequalizer Y)
```

### In an equivalence of coforks, one cofork is a coequalizer if and only if the other is

In other words, given two coforks connected vertically with equivalences, as in
the following diagram:

Given an
[equivalence of coforks](synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.md)
between coforks `c` and `c'`

```text
           ≃
     A --------> A'
    | |         | |
  f | | g    f' | | g'
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> B'
     |     ≃     |
   c |           | c'
     |           |
     ∨           ∨
     X --------> Y ,
           ≃
```

we have that the left cofork is a coequalizer if and only if the right cofork is
a coequalizer.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (e : equiv-double-arrow a a') (e' : equiv-cofork-equiv-double-arrow c c' e)
  where

  universal-property-coequalizer-equiv-cofork-equiv-double-arrow :
    universal-property-coequalizer a' c' →
    universal-property-coequalizer a c
  universal-property-coequalizer-equiv-cofork-equiv-double-arrow up-c' =
    universal-property-coequalizer-universal-property-pushout a c
      ( universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
        ( vertical-map-span-cocone-cofork a')
        ( horizontal-map-span-cocone-cofork a')
        ( horizontal-map-cocone-cofork a' c')
        ( vertical-map-cocone-cofork a' c')
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( horizontal-map-cocone-cofork a c)
        ( vertical-map-cocone-cofork a c)
        ( equiv-coproduct
          ( domain-equiv-equiv-double-arrow a a' e)
          ( domain-equiv-equiv-double-arrow a a' e))
        ( domain-equiv-equiv-double-arrow a a' e)
        ( codomain-equiv-equiv-double-arrow a a' e)
        ( equiv-equiv-cofork-equiv-double-arrow c c' e e')
        ( coherence-square-cocone-cofork a c)
        ( inv-htpy
          ( left-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e)))
        ( inv-htpy
          ( right-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e)))
        ( inv-htpy
          ( pasting-vertical-coherence-square-maps
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( map-cofork a c)
            ( map-cofork a' c')
            ( map-equiv-cofork-equiv-double-arrow c c' e e')
            ( left-square-equiv-double-arrow a a' e)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e')))
        ( inv-htpy (coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e'))
        ( coherence-square-cocone-cofork a' c')
        ( coherence-cube-maps-rotate-120
          ( horizontal-map-cocone-cofork a c)
          ( domain-map-equiv-double-arrow a a' e)
          ( map-equiv-cofork-equiv-double-arrow c c' e e')
          ( horizontal-map-cocone-cofork a' c')
          ( horizontal-map-span-cocone-cofork a)
          ( spanning-map-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( codomain-map-equiv-double-arrow a a' e)
          ( horizontal-map-span-cocone-cofork a')
          ( vertical-map-span-cocone-cofork a)
          ( vertical-map-cocone-cofork a c)
          ( vertical-map-span-cocone-cofork a')
          ( vertical-map-cocone-cofork a' c')
          ( right-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( coherence-square-cocone-cofork a c)
          ( left-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e')
          ( coherence-square-cocone-cofork a' c')
          ( pasting-vertical-coherence-square-maps
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( map-cofork a c)
            ( map-cofork a' c')
            ( map-equiv-cofork-equiv-double-arrow c c' e e')
            ( left-square-equiv-double-arrow a a' e)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e'))
          ( inv-htpy
            ( ind-coproduct _
              ( right-unit-htpy)
              ( coh-equiv-cofork-equiv-double-arrow c c' e e'))))
        ( universal-property-pushout-universal-property-coequalizer a' c'
          ( up-c')))

  universal-property-coequalizer-equiv-cofork-equiv-double-arrow' :
    universal-property-coequalizer a c →
    universal-property-coequalizer a' c'
  universal-property-coequalizer-equiv-cofork-equiv-double-arrow' up-c =
    universal-property-coequalizer-universal-property-pushout a' c'
      ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
        ( vertical-map-span-cocone-cofork a')
        ( horizontal-map-span-cocone-cofork a')
        ( horizontal-map-cocone-cofork a' c')
        ( vertical-map-cocone-cofork a' c')
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( horizontal-map-cocone-cofork a c)
        ( vertical-map-cocone-cofork a c)
        ( spanning-map-hom-span-diagram-cofork-hom-double-arrow a a'
          ( hom-equiv-double-arrow a a' e))
        ( domain-map-equiv-double-arrow a a' e)
        ( codomain-map-equiv-double-arrow a a' e)
        ( map-equiv-cofork-equiv-double-arrow c c' e e')
        ( coherence-square-cocone-cofork a c)
        ( inv-htpy
          ( left-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e)))
        ( inv-htpy
          ( right-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e)))
        ( inv-htpy
          ( pasting-vertical-coherence-square-maps
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( map-cofork a c)
            ( map-cofork a' c')
            ( map-equiv-cofork-equiv-double-arrow c c' e e')
            ( left-square-equiv-double-arrow a a' e)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e')))
        ( inv-htpy (coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e'))
        ( coherence-square-cocone-cofork a' c')
        ( coherence-cube-maps-rotate-120
          ( horizontal-map-cocone-cofork a c)
          ( domain-map-equiv-double-arrow a a' e)
          ( map-equiv-cofork-equiv-double-arrow c c' e e')
          ( horizontal-map-cocone-cofork a' c')
          ( horizontal-map-span-cocone-cofork a)
          ( spanning-map-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( codomain-map-equiv-double-arrow a a' e)
          ( horizontal-map-span-cocone-cofork a')
          ( vertical-map-span-cocone-cofork a)
          ( vertical-map-cocone-cofork a c)
          ( vertical-map-span-cocone-cofork a')
          ( vertical-map-cocone-cofork a' c')
          ( right-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( coherence-square-cocone-cofork a c)
          ( left-square-hom-span-diagram-cofork-hom-double-arrow a a'
            ( hom-equiv-double-arrow a a' e))
          ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e')
          ( coherence-square-cocone-cofork a' c')
          ( pasting-vertical-coherence-square-maps
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( map-cofork a c)
            ( map-cofork a' c')
            ( map-equiv-cofork-equiv-double-arrow c c' e e')
            ( left-square-equiv-double-arrow a a' e)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrow c c' e e'))
          ( inv-htpy
            ( ind-coproduct _
              ( right-unit-htpy)
              ( coh-equiv-cofork-equiv-double-arrow c c' e e'))))
        ( is-equiv-map-coproduct
          ( is-equiv-domain-map-equiv-double-arrow a a' e)
          ( is-equiv-domain-map-equiv-double-arrow a a' e))
        ( is-equiv-domain-map-equiv-double-arrow a a' e)
        ( is-equiv-codomain-map-equiv-double-arrow a a' e)
        ( is-equiv-map-equiv-cofork-equiv-double-arrow c c' e e')
        ( universal-property-pushout-universal-property-coequalizer a c up-c))
```
