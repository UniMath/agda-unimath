# The universal property of equalizers

```agda
module foundation.universal-property-equalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.equivalences-forks-over-equivalences-double-arrows
open import foundation.fibers-of-maps
open import foundation.forks
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
```

</details>

## Idea

Given a [double arrow](foundation.double-arrows.md) `f, g : A → B`, consider a
[fork](foundation.forks.md) `e : B → X` with vertex `X`. The
{{#concept "universal property" Disambiguation="of equalizers of types" Agda=universal-property-equalizer}}
of [equalizers](foundation.equalizers.md) is the statement that the fork
postcomposition map

```text
fork-map : (X → Y) → fork Y
```

is an [equivalence](foundation.equivalences.md).

## Definitions

### The universal property of equalizers

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X)
  where

  universal-property-equalizer : UUω
  universal-property-equalizer =
    {l : Level} (Y : UU l) → is-equiv (fork-map a e {Y = Y})

module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X) {Y : UU l4}
  (up-equalizer : universal-property-equalizer a e)
  where

  map-universal-property-equalizer : fork a Y → (Y → X)
  map-universal-property-equalizer = map-inv-is-equiv (up-equalizer Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X) {Y : UU l4}
  (up-equalizer : universal-property-equalizer a e)
  (e' : fork a Y)
  where

  htpy-fork-map-universal-property-equalizer :
    htpy-fork a
      ( fork-map a e
        ( map-universal-property-equalizer a e up-equalizer e'))
      ( e')
  htpy-fork-map-universal-property-equalizer =
    htpy-fork-eq a
      ( fork-map a e
        ( map-universal-property-equalizer a e up-equalizer e'))
      ( e')
      ( is-section-map-inv-is-equiv (up-equalizer Y) e')

  abstract
    uniqueness-map-universal-property-equalizer :
      is-contr (Σ (Y → X) (λ h → htpy-fork a (fork-map a e h) e'))
    uniqueness-map-universal-property-equalizer =
      is-contr-is-equiv'
        ( fiber (fork-map a e) e')
        ( tot (λ h → htpy-fork-eq a (fork-map a e h) e'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h → is-equiv-htpy-fork-eq a (fork-map a e h) e'))
        ( is-contr-map-is-equiv (up-equalizer Y) e')
```

### A fork has the universal property of equalizers if and only if the corresponding cone has the universal property of pullbacks

As mentioned in [`forks`](foundation.forks.md), forks can be thought of as
special cases of cones under cospans. This theorem makes it more precise,
asserting that under this mapping, [equalizers](foundation.equalizers.md)
correspond to [pullbacks](foundation.pullbacks.md).

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X)
  where

  universal-property-equalizer-universal-property-pullback :
    universal-property-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( cone-diagonal-fork a e) →
      universal-property-equalizer a e
  universal-property-equalizer-universal-property-pullback up-pullback Y =
    is-equiv-left-map-triangle
      ( fork-map a e)
      ( fork-cone-diagonal a)
      ( cone-map
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( cone-diagonal-fork a e))
      ( triangle-fork-cone a e)
      ( up-pullback Y)
      ( is-equiv-fork-cone-diagonal a)

  universal-property-pullback-universal-property-equalizer :
    universal-property-equalizer a e →
    universal-property-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( cone-diagonal-fork a e)
  universal-property-pullback-universal-property-equalizer up-equalizer Y =
    is-equiv-top-map-triangle
      ( fork-map a e)
      ( fork-cone-diagonal a)
      ( cone-map
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( cone-diagonal-fork a e))
      ( triangle-fork-cone a e)
      ( is-equiv-fork-cone-diagonal a)
      ( up-equalizer Y)
```

### In an equivalence of forks, one fork is a equalizer if and only if the other is

In other words, given two forks connected vertically with equivalences, as in
the following diagram:

Given an
[equivalence of forks](foundation.equivalences-forks-over-equivalences-double-arrows.md)
between forks `c` and `c'`

```text
           ≃
     X --------> Y
     |           |
   c |           | c'
     |           |
     ∨     ≃     ∨
     A --------> U
    | |         | |
  f | | g     h | | k
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> V
           ≃
```

we have that the left fork is a equalizer if and only if the right fork is a
equalizer.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : fork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : fork a' Y)
  (e : equiv-double-arrow a a') (e' : equiv-fork-equiv-double-arrow a a' c c' e)
  where

  abstract
    coherence-cube-cone-fork-equiv-double-arrow :
      coherence-cube-maps
        ( horizontal-map-cone-fork a' c')
        ( vertical-map-cone-fork a' c')
        ( vertical-map-cospan-cone-fork a')
        ( horizontal-map-cospan-cone-fork a')
        ( horizontal-map-cone-fork a c)
        ( vertical-map-cone-fork a c)
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( map-equiv
          ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
        ( map-equiv (codomain-equiv-equiv-double-arrow a a' e))
        ( map-equiv (domain-equiv-equiv-double-arrow a a' e))
        ( map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e)))
        ( coherence-square-cone-fork a c)
        ( inv-htpy
          ( pasting-vertical-coherence-square-maps
            ( map-equiv
              ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
            ( map-fork a c)
            ( map-fork a' c')
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
            ( left-square-equiv-double-arrow a a' e)))
        ( inv-htpy (coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e'))
        ( inv-htpy
          ( right-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e))
        ( inv-htpy
          ( inv-htpy
            ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)))
        ( coherence-square-cone-fork a' c')
    coherence-cube-cone-fork-equiv-double-arrow =
      coherence-cube-maps-rotate-120
        ( vertical-map-cospan-cone-fork a)
        ( codomain-map-equiv-double-arrow a a' e)
        ( map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e)))
        ( vertical-map-cospan-cone-fork a')
        ( vertical-map-cone-fork a c)
        ( map-equiv
          ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
        ( domain-map-equiv-double-arrow a a' e)
        ( vertical-map-cone-fork a' c')
        ( horizontal-map-cone-fork a c)
        ( horizontal-map-cospan-cone-fork a)
        ( horizontal-map-cone-fork a' c')
        ( horizontal-map-cospan-cone-fork a')
        ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
        ( coherence-square-cone-fork a c)
        ( pasting-vertical-coherence-square-maps
          ( map-equiv
            ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
          ( map-fork a c)
          ( map-fork a' c')
          ( domain-map-equiv-double-arrow a a' e)
          ( left-map-double-arrow a)
          ( left-map-double-arrow a')
          ( codomain-map-equiv-double-arrow a a' e)
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( left-square-equiv-double-arrow a a' e))
        ( inv-htpy
          ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e))
        ( coherence-square-cone-fork a' c')
        ( right-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)
        ( coherence-cube-cone-fork-equiv-fork-equiv-double-arrow c c' e e')

  abstract
    universal-property-pullback-equiv-fork-equiv-double-arrow :
      universal-property-pullback
        ( vertical-map-cospan-cone-fork a')
        ( horizontal-map-cospan-cone-fork a')
        ( cone-diagonal-fork a' c') →
      universal-property-pullback
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( cone-diagonal-fork a c)
    universal-property-pullback-equiv-fork-equiv-double-arrow =
      universal-property-pullback-top-universal-property-pullback-bottom-cube-equiv
        ( horizontal-map-cone-fork a' c')
        ( vertical-map-cone-fork a' c')
        ( vertical-map-cospan-cone-fork a')
        ( horizontal-map-cospan-cone-fork a')
        ( horizontal-map-cone-fork a c)
        ( vertical-map-cone-fork a c)
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e')
        ( codomain-equiv-equiv-double-arrow a a' e)
        ( domain-equiv-equiv-double-arrow a a' e)
        ( equiv-product
          ( codomain-equiv-equiv-double-arrow a a' e)
          ( codomain-equiv-equiv-double-arrow a a' e))
        ( coherence-square-cone-fork a c)
        ( inv-htpy
          ( pasting-vertical-coherence-square-maps
            ( map-equiv
              ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
            ( map-fork a c)
            ( map-fork a' c')
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
            ( left-square-equiv-double-arrow a a' e)))
        ( inv-htpy (coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e'))
        ( inv-htpy
          ( right-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e))
        ( inv-htpy
          ( inv-htpy
            ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)))
        ( coherence-square-cone-fork a' c')
        ( coherence-cube-cone-fork-equiv-double-arrow)

  abstract
    universal-property-pullback-equiv-fork-equiv-double-arrow' :
      universal-property-pullback
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( cone-diagonal-fork a c) →
      universal-property-pullback
        ( vertical-map-cospan-cone-fork a')
        ( horizontal-map-cospan-cone-fork a')
        ( cone-diagonal-fork a' c')
    universal-property-pullback-equiv-fork-equiv-double-arrow' =
      universal-property-pullback-bottom-universal-property-pullback-top-cube-equiv
        ( horizontal-map-cone-fork a' c')
        ( vertical-map-cone-fork a' c')
        ( vertical-map-cospan-cone-fork a')
        ( horizontal-map-cospan-cone-fork a')
        ( horizontal-map-cone-fork a c)
        ( vertical-map-cone-fork a c)
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e')
        ( codomain-equiv-equiv-double-arrow a a' e)
        ( domain-equiv-equiv-double-arrow a a' e)
        ( equiv-product
          ( codomain-equiv-equiv-double-arrow a a' e)
          ( codomain-equiv-equiv-double-arrow a a' e))
        ( coherence-square-cone-fork a c)
        ( inv-htpy
          ( pasting-vertical-coherence-square-maps
            ( map-equiv
              ( equiv-equiv-fork-equiv-double-arrow a a' c c' e e'))
            ( map-fork a c)
            ( map-fork a' c')
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
            ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
            ( left-square-equiv-double-arrow a a' e)))
        ( inv-htpy (coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e'))
        ( inv-htpy
          ( right-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e))
        ( inv-htpy
          ( inv-htpy
            ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)))
        ( coherence-square-cone-fork a' c')
        ( coherence-cube-cone-fork-equiv-double-arrow)

  abstract
    universal-property-equalizer-equiv-fork-equiv-double-arrow :
      universal-property-equalizer a' c' →
      universal-property-equalizer a c
    universal-property-equalizer-equiv-fork-equiv-double-arrow up-c' =
      universal-property-equalizer-universal-property-pullback a c
        ( universal-property-pullback-equiv-fork-equiv-double-arrow
          ( universal-property-pullback-universal-property-equalizer a' c'
            ( up-c')))

  abstract
    universal-property-equalizer-equiv-fork-equiv-double-arrow' :
      universal-property-equalizer a c →
      universal-property-equalizer a' c'
    universal-property-equalizer-equiv-fork-equiv-double-arrow' up-c =
      universal-property-equalizer-universal-property-pullback a' c'
        ( universal-property-pullback-equiv-fork-equiv-double-arrow'
          ( universal-property-pullback-universal-property-equalizer a c
            ( up-c)))
```
