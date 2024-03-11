# Transposition of cocones under span diagrams

```agda
module synthetic-homotopy-theory.transposition-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Any cocone

```text
        g
    S -----> B
    |        |
  f |        | j
    V        V
    A -----> X
        i
```

induces a cocone

```text
        f
    S -----> A
    |        |
  g |        | i
    V        V
    B -----> X.
        j
```

This {{#concept "transposition" Disambiguation="cocones under span diagrams"}}
on cocones is an [involution](foundation.involutions.md).

## Definitions

### Transposing cocones under span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  transposition-cocone-span-diagram :
    cocone-span-diagram 𝒮 X →
    cocone-span-diagram (transposition-span-diagram 𝒮) X
  pr1 (transposition-cocone-span-diagram c) =
    right-map-cocone-span-diagram 𝒮 c
  pr1 (pr2 (transposition-cocone-span-diagram c)) =
    left-map-cocone-span-diagram 𝒮 c
  pr2 (pr2 (transposition-cocone-span-diagram c)) =
    inv-htpy (coherence-square-cocone-span-diagram 𝒮 c)
```

## Properties

### Transposition of cocones under span diagrams is an involution

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-involution-transposition-cocone-span-diagram :
    transposition-cocone-span-diagram (transposition-span-diagram 𝒮) {X} ∘
    transposition-cocone-span-diagram 𝒮 {X} ~
    id
  is-involution-transposition-cocone-span-diagram c =
    eq-htpy-cocone-span-diagram 𝒮
      ( transposition-cocone-span-diagram
        ( transposition-span-diagram 𝒮)
        ( transposition-cocone-span-diagram 𝒮 c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ t →
          concat
            ( right-unit)
            ( coherence-square-cocone-span-diagram 𝒮 c t)
            ( inv-inv (coherence-square-cocone-span-diagram 𝒮 c t))))
```

### Transposition of cocones under span diagrams is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-equiv-transposition-cocone-span-diagram :
    is-equiv (transposition-cocone-span-diagram 𝒮 {X})
  is-equiv-transposition-cocone-span-diagram =
    is-equiv-is-invertible
      ( transposition-cocone-span-diagram (transposition-span-diagram 𝒮))
      ( is-involution-transposition-cocone-span-diagram
        ( transposition-span-diagram 𝒮)
        ( X))
      ( is-involution-transposition-cocone-span-diagram 𝒮 X)

  equiv-transposition-cocone-span-diagram :
    cocone-span-diagram 𝒮 X ≃
    cocone-span-diagram (transposition-span-diagram 𝒮) X
  pr1 equiv-transposition-cocone-span-diagram =
    transposition-cocone-span-diagram 𝒮
  pr2 equiv-transposition-cocone-span-diagram =
    is-equiv-transposition-cocone-span-diagram
```
