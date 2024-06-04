# Descent data for type families of identity types over pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.descent-data-identity-types-over-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
```

</details>

## Idea

Given a [cocone](synthetic-homotopy-theory.cocones-under-spans.md) under a
[span diagram](foundation.span-diagrams.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

and a point `x₀ : X`, the type family of
[identity types](foundation-core.identity-types.md) based at `x₀`,
`x ↦ (x₀ = x)`, is
[characterized](synthetic-homotopy-theory.families-descent-data-pushouts.md) by
the [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
`(IA, IB, IS)`, where `IA` and `IB` are families of identity types

```text
  IA a := (x₀ = ia)
  IB b := (x₀ = jb),
```

and the gluing data `IS s : (x₀ = ifs) ≃ (x₀ = jgs)` is given by concatenation
with the coherence of the cocone `H s : ifs = jgs`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (x₀ : X)
  where

  family-cocone-family-with-descent-data-pushout-identity-type : X → UU l4
  family-cocone-family-with-descent-data-pushout-identity-type x =
    x₀ ＝ x

  descent-data-pushout-identity-type : descent-data-pushout 𝒮 l4
  pr1 descent-data-pushout-identity-type a =
    x₀ ＝ horizontal-map-cocone _ _ c a
  pr1 (pr2 descent-data-pushout-identity-type) b =
    x₀ ＝ vertical-map-cocone _ _ c b
  pr2 (pr2 descent-data-pushout-identity-type) s =
    equiv-concat' x₀ (coherence-square-cocone _ _ c s)

  equiv-descent-data-pushout-identity-type :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout-identity-type))
      ( descent-data-pushout-identity-type)
  pr1 equiv-descent-data-pushout-identity-type a = id-equiv
  pr1 (pr2 equiv-descent-data-pushout-identity-type) b = id-equiv
  pr2 (pr2 equiv-descent-data-pushout-identity-type) s =
    tr-Id-right (coherence-square-cocone _ _ c s)

  family-with-descent-data-pushout-identity-type :
    family-with-descent-data-pushout c l4
  pr1 family-with-descent-data-pushout-identity-type =
    family-cocone-family-with-descent-data-pushout-identity-type
  pr1 (pr2 family-with-descent-data-pushout-identity-type) =
    descent-data-pushout-identity-type
  pr2 (pr2 family-with-descent-data-pushout-identity-type) =
    equiv-descent-data-pushout-identity-type
```
