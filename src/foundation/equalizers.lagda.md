# Equalizers

```agda
module foundation.equalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-arrows
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation.forks
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.universal-property-equalizers
open import foundation.universal-property-pullbacks
```

</details>

## Idea

The **equalizer** of a [double arrow](foundation.double-arrows.md)
`f, g : A → B` is a [fork](foundation.forks.md) that satisfies the
[universal property of equalizers](foundation.universal-property-equalizers.md).

## Properties

### All double arrows admit a equalizer

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
      ( λ c →
        is-pullback
          ( vertical-map-cospan-cone-fork a)
          ( horizontal-map-cospan-cone-fork a)
          ( c))
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
