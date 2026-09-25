# Standard equalizers

```agda
module foundation.standard-equalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-arrows
open import foundation.forks
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.universal-property-equalizers
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "standard equalizer" Disambiguation="of a double arrow of types" WDID=Q1224487 WD="equaliser" Agda=standard-equalizer}}
of a [double arrow](foundation.double-arrows.md) `f, g : A → B` is the type of
pairs of elements `x, y : A` such that `f x ＝ g y`. It comes equipped with a
canonical [fork](foundation.forks.md) satisfying the
[universal property of equalizers](foundation.universal-property-equalizers.md)
between `f` and `g`.

## Properties

### All double arrows admit an equalizer

```agda
module _
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  standard-equalizer : UU (l1 ⊔ l2)
  standard-equalizer =
    standard-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)

  fork-standard-equalizer : fork a standard-equalizer
  fork-standard-equalizer =
    fork-cone-diagonal a
      ( cone-standard-pullback
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a))

  is-pullback-cone-standard-equalizer :
    is-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( cone-diagonal-fork a fork-standard-equalizer)
  is-pullback-cone-standard-equalizer =
    tr
      ( is-pullback
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a))
      ( inv
        ( is-retraction-cone-diagonal-fork a
          ( cone-standard-pullback
            ( vertical-map-cospan-cone-fork a)
            ( horizontal-map-cospan-cone-fork a))))
      ( is-pullback-universal-property-pullback
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( cone-standard-pullback
          ( vertical-map-cospan-cone-fork a)
          ( horizontal-map-cospan-cone-fork a))
        ( universal-property-standard-pullback
          ( vertical-map-cospan-cone-fork a)
          ( horizontal-map-cospan-cone-fork a)))

  up-cone-standard-equalizer :
    universal-property-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( cone-diagonal-fork a fork-standard-equalizer)
  up-cone-standard-equalizer =
    universal-property-pullback-is-pullback
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( cone-diagonal-fork a fork-standard-equalizer)
      ( is-pullback-cone-standard-equalizer)

  up-standard-equalizer :
    universal-property-equalizer a fork-standard-equalizer
  up-standard-equalizer =
    universal-property-equalizer-universal-property-pullback a
      ( fork-standard-equalizer)
      ( up-cone-standard-equalizer)
```
