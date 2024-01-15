# The dependent universal property of pushouts

```agda
module synthetic-homotopy-theory.dependent-universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
```

</details>

## Idea

The {{#concept "dependent universal property of pushouts"}} asserts that every
section of a type family over a [pushout](synthetic-homotopy-theory.pushouts.md)
corresponds in a canonical way uniquely to a
[dependent cocone](synthetic-homotopy-theory.dependent-cocones-under-span-diagrams.md)
over the
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) on
the pushout. In other words, it assserts that the canonical map

```text
  ((x : X) → P x) → dependent-cocone-span-diagram s c P
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

### The dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  dependent-universal-property-pushout : UUω
  dependent-universal-property-pushout =
    {l : Level} (P : X → UU l) →
    is-equiv (dependent-cocone-map-span-diagram 𝒮 c P)

  module _
    (U : dependent-universal-property-pushout)
    {l : Level} (P : X → UU l)
    where

    abstract
      map-dependent-universal-property-pushout :
        dependent-cocone-span-diagram 𝒮 c P → ((x : X) → P x)
      map-dependent-universal-property-pushout =
        map-inv-is-equiv (U P)

      compute-map-dependent-universal-property-pushout :
        (d : dependent-cocone-span-diagram 𝒮 c P) →
        htpy-dependent-cocone-span-diagram 𝒮 c P
          ( dependent-cocone-map-span-diagram 𝒮 c P
            ( map-dependent-universal-property-pushout d))
          ( d)
      compute-map-dependent-universal-property-pushout d =
        htpy-eq-dependent-cocone-span-diagram 𝒮 c P
          ( dependent-cocone-map-span-diagram 𝒮 c P
            ( map-dependent-universal-property-pushout d))
          ( d)
          ( is-section-map-inv-is-equiv (U P) d)
```

## Properties

### Sections defined by the dependent universal property are unique up to homotopy

```agda
module _
  { l1 l2 l3 l4 l : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} ( c : cocone-span-diagram 𝒮 X)
  ( U : dependent-universal-property-pushout 𝒮 c)
  ( P : X → UU l) (h : dependent-cocone-span-diagram 𝒮 c P)
  where

  abstract
    uniqueness-dependent-universal-property-pushout :
      is-contr
        ( Σ ( (x : X) → P x)
            ( λ k →
              htpy-dependent-cocone-span-diagram 𝒮 c P
                ( dependent-cocone-map-span-diagram 𝒮 c P k)
                ( h)))
    uniqueness-dependent-universal-property-pushout =
      is-contr-equiv'
        ( fiber (dependent-cocone-map-span-diagram 𝒮 c P) h)
        ( equiv-tot
          ( λ k →
            extensionality-dependent-cocone-span-diagram 𝒮 c P
              ( dependent-cocone-map-span-diagram 𝒮 c P k)
              ( h)))
        ( is-contr-map-is-equiv (U P) h)
```

### The induction principle of pushouts is equivalent to the dependent universal property of pushouts

#### The induction principle of pushouts implies the dependent universal property of pushouts

```agda
module _
  { l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X)
  ( H : induction-principle-pushout 𝒮 c)
  where

  htpy-eq-dependent-cocone-map-span-diagram :
    {l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
    dependent-cocone-map-span-diagram 𝒮 c P h ＝
    dependent-cocone-map-span-diagram 𝒮 c P h' →
    h ~ h'
  htpy-eq-dependent-cocone-map-span-diagram {l} {P} h h' p =
    ind-induction-principle-pushout 𝒮 c H
      ( λ x → Id (h x) (h' x))
      ( pair
        ( left-htpy-eq-dependent-cocone-span-diagram 𝒮 c P
          ( dependent-cocone-map-span-diagram 𝒮 c P h)
          ( dependent-cocone-map-span-diagram 𝒮 c P h')
          ( p))
        ( pair
          ( right-htpy-eq-dependent-cocone-span-diagram 𝒮 c P
            ( dependent-cocone-map-span-diagram 𝒮 c P h)
            ( dependent-cocone-map-span-diagram 𝒮 c P h')
            ( p))
          ( λ s →
            map-compute-dependent-identification-eq-value h h'
              ( coherence-square-cocone-span-diagram 𝒮 c s)
              ( left-htpy-eq-dependent-cocone-span-diagram 𝒮 c P
                ( dependent-cocone-map-span-diagram 𝒮 c P h)
                ( dependent-cocone-map-span-diagram 𝒮 c P h')
                ( p)
                ( left-map-span-diagram 𝒮 s))
              ( right-htpy-eq-dependent-cocone-span-diagram 𝒮 c P
                ( dependent-cocone-map-span-diagram 𝒮 c P h)
                ( dependent-cocone-map-span-diagram 𝒮 c P h')
                ( p)
                ( right-map-span-diagram 𝒮 s))
              ( coherence-square-htpy-eq-dependent-cocone-span-diagram 𝒮 c P
                ( dependent-cocone-map-span-diagram 𝒮 c P h)
                ( dependent-cocone-map-span-diagram 𝒮 c P h')
                ( p)
                ( s)))))

  dependent-universal-property-pushout-induction-principle-pushout :
    dependent-universal-property-pushout 𝒮 c
  dependent-universal-property-pushout-induction-principle-pushout P =
    is-equiv-is-invertible
      ( ind-induction-principle-pushout 𝒮 c H P)
      ( eq-compute-ind-induction-principle-pushout 𝒮 c H P)
      ( λ h →
        eq-htpy
          ( htpy-eq-dependent-cocone-map-span-diagram
            ( ind-induction-principle-pushout 𝒮 c H P
              ( dependent-cocone-map-span-diagram 𝒮 c P h))
            ( h)
            ( eq-compute-ind-induction-principle-pushout 𝒮 c H P
              ( dependent-cocone-map-span-diagram 𝒮 c P h))))
```

#### The dependent universal property of pushouts implies the induction principle of pushouts

```agda
induction-principle-pushout-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) →
  dependent-universal-property-pushout 𝒮 c →
  induction-principle-pushout 𝒮 c
induction-principle-pushout-dependent-universal-property-pushout 𝒮 c U P =
  pr1 (U P)
```

### The dependent pullback property of pushouts is equivalent to the dependent universal property of pushouts

#### The dependent universal property of pushouts implies the dependent pullback property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  triangle-dependent-pullback-property-pushout :
    {l5 : Level} (P : X → UU l5) →
    coherence-triangle-maps
      ( dependent-cocone-map-span-diagram 𝒮 c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ ( h :
              ( a : domain-span-diagram 𝒮) →
              P (left-map-cocone-span-diagram 𝒮 c a))
            ( s : spanning-type-span-diagram 𝒮) →
          tr P
            ( coherence-square-cocone-span-diagram 𝒮 c s)
            ( h (left-map-span-diagram 𝒮 s)))
        ( λ ( h :
              ( b : codomain-span-diagram 𝒮) →
              P (right-map-cocone-span-diagram 𝒮 c b))
            ( s : spanning-type-span-diagram 𝒮) →
          h (right-map-span-diagram 𝒮 s))
        ( cone-dependent-pullback-property-pushout 𝒮 c P))
  triangle-dependent-pullback-property-pushout P h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( inv
          ( is-section-eq-htpy
            ( apd h ∘ coherence-square-cocone-span-diagram 𝒮 c))))

  dependent-pullback-property-dependent-universal-property-pushout :
    dependent-universal-property-pushout 𝒮 c →
    dependent-pullback-property-pushout 𝒮 c
  dependent-pullback-property-dependent-universal-property-pushout I P =
    is-equiv-top-map-triangle
      ( dependent-cocone-map-span-diagram 𝒮 c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ h s →
          tr P
            ( coherence-square-cocone-span-diagram 𝒮 c s)
            ( h (left-map-span-diagram 𝒮 s)))
        ( _∘ right-map-span-diagram 𝒮)
        ( cone-dependent-pullback-property-pushout 𝒮 c P))
        ( triangle-dependent-pullback-property-pushout P)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-tot-is-fiberwise-equiv
          ( λ h' →
            funext
              ( λ s →
                tr P
                  ( coherence-square-cocone-span-diagram 𝒮 c s)
                  ( h (left-map-span-diagram 𝒮 s)))
              ( h' ∘ right-map-span-diagram 𝒮))))
      ( I P)
```

#### The dependent pullback property of pushouts implies the dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  dependent-universal-property-dependent-pullback-property-pushout :
    dependent-pullback-property-pushout 𝒮 c →
    dependent-universal-property-pushout 𝒮 c
  dependent-universal-property-dependent-pullback-property-pushout U P =
    is-equiv-left-map-triangle
      ( dependent-cocone-map-span-diagram 𝒮 c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ h s →
          tr P
            ( coherence-square-cocone-span-diagram 𝒮 c s)
            ( h (left-map-span-diagram 𝒮 s)))
        ( _∘ right-map-span-diagram 𝒮)
        ( cone-dependent-pullback-property-pushout 𝒮 c P))
      ( triangle-dependent-pullback-property-pushout 𝒮 c P)
      ( U P)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h →
          is-equiv-tot-is-fiberwise-equiv
            ( λ h' →
              funext
                ( λ s →
                  tr P
                    ( coherence-square-cocone-span-diagram 𝒮 c s)
                    ( h (left-map-span-diagram 𝒮 s)))
                ( h' ∘ right-map-span-diagram 𝒮))))
```
