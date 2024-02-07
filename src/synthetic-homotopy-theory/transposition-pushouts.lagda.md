# Transposition of pushouts

```agda
module synthetic-homotopy-theory.transposition-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types

open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.transposition-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

If a [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

is a [pushout square](synthetic-homotopy-theory.pushouts.md), then so is the [transposed square](synthetic-homotopy-theory.transposition-cocones-under-span-diagrams.md)

```text
        f
    S -----> A
    |        |
  g |        | i
    ∨        ∨
    B -----> X.
        j
```

## Properties

### Transposing a pushout cocone yields another pushout cocone

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (X : UU l4) (c : cocone-span-diagram 𝒮 X)
  where

  universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout :
    universal-property-pushout 𝒮 c →
    universal-property-pushout
      ( transposition-span-diagram 𝒮)
      ( transposition-cocone-span-diagram 𝒮 c)
  universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout
    up Y =
    is-equiv-equiv'
      ( id-equiv)
      ( equiv-transposition-cocone-span-diagram 𝒮 Y)
      ( λ h →
        eq-htpy-cocone-span-diagram
          ( transposition-span-diagram 𝒮)
          ( transposition-cocone-span-diagram 𝒮
            ( cocone-map-span-diagram 𝒮 c h))
          ( cocone-map-span-diagram
            ( transposition-span-diagram 𝒮)
            ( transposition-cocone-span-diagram 𝒮 c)
            ( h))
          ( ( refl-htpy) ,
            ( refl-htpy) ,
            ( λ x →
              right-unit ∙
              inv (ap-inv h (coherence-square-cocone-span-diagram 𝒮 c x)))))
      ( up Y)

  is-pushout-transposition-cocone-span-diagram-is-pushout :
    is-pushout 𝒮 c →
    is-pushout
      ( transposition-span-diagram 𝒮)
      ( transposition-cocone-span-diagram 𝒮 c)
  is-pushout-transposition-cocone-span-diagram-is-pushout H =
    is-pushout-universal-property-pushout (transposition-span-diagram 𝒮)
      ( transposition-cocone-span-diagram 𝒮 c)
      ( universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout
        ( universal-property-pushout-is-pushout 𝒮 c H))
```

