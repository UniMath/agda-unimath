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
open import foundation.spans
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
```

</details>

## Idea

The **dependent universal property of pushouts** asserts that every section of a
type family over a [pushout](synthetic-homotopy-theory.pushouts.md) corresponds
in a canonical way uniquely to a
[dependent cocone](synthetic-homotopy-theory.dependent-cocones-under-span-diagrams.md)
over the
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) on
the pushout.

## Definition

### The dependent universal property of pushouts

```agda
dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} (c : cocone-span s X) →
  UUω
dependent-universal-property-pushout s {X} c =
  {l : Level} (P : X → UU l) → is-equiv (dependent-cocone-span-map s c P)
```

## Properties

### Sections defined by the dependent universal property are unique up to homotopy

```agda
module _
  { l1 l2 l3 l4 l : Level} (s : span l1 l2 l3)
  { X : UU l4} ( c : cocone-span s X)
  ( U : dependent-universal-property-pushout s c)
  ( P : X → UU l) (h : dependent-cocone-span s c P)
  where

  abstract
    uniqueness-dependent-universal-property-pushout :
      is-contr
        ( Σ ( (x : X) → P x)
            ( λ k →
              htpy-dependent-cocone-span s c P
                ( dependent-cocone-span-map s c P k)
                ( h)))
    uniqueness-dependent-universal-property-pushout =
      is-contr-is-equiv'
        ( fiber (dependent-cocone-span-map s c P) h)
        ( tot
          ( λ k →
            htpy-eq-dependent-cocone-span s c P
              ( dependent-cocone-span-map s c P k)
              ( h)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ k →
            is-equiv-htpy-eq-dependent-cocone-span s c P
              ( dependent-cocone-span-map s c P k)
              ( h)))
        ( is-contr-map-is-equiv (U P) h)
```

### The induction principle of pushouts is equivalent to the dependent universal property of pushouts

#### The induction principle of pushouts implies the dependent universal property of pushouts

```agda
module _
  { l1 l2 l3 l4 : Level} (s : span l1 l2 l3)
  { X : UU l4} (c : cocone-span s X)
  ( H : induction-principle-pushout s c)
  where

  htpy-eq-dependent-cocone-span-map :
    {l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
    dependent-cocone-span-map s c P h ＝ dependent-cocone-span-map s c P h' →
    h ~ h'
  htpy-eq-dependent-cocone-span-map {l} {P} h h' p =
    ind-induction-principle-pushout s c H
      ( λ x → Id (h x) (h' x))
      ( pair
        ( horizontal-htpy-eq-dependent-cocone-span s c P
          ( dependent-cocone-span-map s c P h)
          ( dependent-cocone-span-map s c P h')
          ( p))
        ( pair
          ( vertical-htpy-eq-dependent-cocone-span s c P
            ( dependent-cocone-span-map s c P h)
            ( dependent-cocone-span-map s c P h')
            ( p))
          ( λ x →
            map-compute-dependent-identification-eq-value h h'
              ( coherence-square-cocone-span s c x)
              ( horizontal-htpy-eq-dependent-cocone-span s c P
                ( dependent-cocone-span-map s c P h)
                ( dependent-cocone-span-map s c P h')
                ( p)
                ( left-map-span s x))
              ( vertical-htpy-eq-dependent-cocone-span s c P
                ( dependent-cocone-span-map s c P h)
                ( dependent-cocone-span-map s c P h')
                ( p)
                ( right-map-span s x))
              ( coherence-square-htpy-eq-dependent-cocone-span s c P
                ( dependent-cocone-span-map s c P h)
                ( dependent-cocone-span-map s c P h')
                ( p)
                ( x)))))

  dependent-universal-property-pushout-induction-principle-pushout :
    dependent-universal-property-pushout s c
  dependent-universal-property-pushout-induction-principle-pushout P =
    is-equiv-is-invertible
      ( ind-induction-principle-pushout s c H P)
      ( pr2 (H P))
      ( λ h →
        eq-htpy
          ( htpy-eq-dependent-cocone-span-map
            ( ind-induction-principle-pushout s c H P
              ( dependent-cocone-span-map s c P h))
            ( h)
            ( pr2 (H P) (dependent-cocone-span-map s c P h))))
```

#### The dependent universal property of pushouts implies the induction principle of pushouts

```agda
induction-principle-pushout-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3)
  {X : UU l4} (c : cocone-span s X) →
  dependent-universal-property-pushout s c →
  induction-principle-pushout s c
induction-principle-pushout-dependent-universal-property-pushout s c U P =
  pr1 (U P)
```

### The dependent pullback property of pushouts is equivalent to the dependent universal property of pushouts

#### The dependent universal property of pushouts implies the dependent pullback property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} (c : cocone-span s X)
  where

  triangle-dependent-pullback-property-pushout :
    {l5 : Level} (P : X → UU l5) →
    coherence-triangle-maps
      ( dependent-cocone-span-map s c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ ( h : (a : domain-span s) → P (horizontal-map-cocone-span s c a))
            ( x : spanning-type-span s) →
            tr P (coherence-square-cocone-span s c x) (h (left-map-span s x)))
        ( λ ( h : (b : codomain-span s) → P (vertical-map-cocone-span s c b))
            ( x : spanning-type-span s) →
            h (right-map-span s x))
        ( cone-dependent-pullback-property-pushout s c P))
  triangle-dependent-pullback-property-pushout P h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( inv (is-section-eq-htpy (apd h ∘ coherence-square-cocone-span s c))))

  dependent-pullback-property-dependent-universal-property-pushout :
    dependent-universal-property-pushout s c →
    dependent-pullback-property-pushout s c
  dependent-pullback-property-dependent-universal-property-pushout I P =
    is-equiv-top-map-triangle
      ( dependent-cocone-span-map s c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ h x →
          tr P (coherence-square-cocone-span s c x) (h (left-map-span s x)))
        ( _∘ right-map-span s)
        ( cone-dependent-pullback-property-pushout s c P))
        ( triangle-dependent-pullback-property-pushout P)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-tot-is-fiberwise-equiv
          ( λ h' →
            funext
              ( λ x →
                tr P
                  ( coherence-square-cocone-span s c x)
                  ( h (left-map-span s x)))
              ( h' ∘ right-map-span s))))
      ( I P)
```

#### The dependent pullback property of pushouts implies the dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} (c : cocone-span s X)
  where

  dependent-universal-property-dependent-pullback-property-pushout :
    dependent-pullback-property-pushout s c →
    dependent-universal-property-pushout s c
  dependent-universal-property-dependent-pullback-property-pushout U P =
    is-equiv-left-map-triangle
      ( dependent-cocone-span-map s c P)
      ( tot (λ h → tot (λ h' → htpy-eq)))
      ( gap
        ( λ h x →
          tr P (coherence-square-cocone-span s c x) (h (left-map-span s x)))
        ( _∘ right-map-span s)
        ( cone-dependent-pullback-property-pushout s c P))
      ( triangle-dependent-pullback-property-pushout s c P)
      ( U P)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h →
          is-equiv-tot-is-fiberwise-equiv
            ( λ h' →
              funext
                ( λ x →
                  tr P
                    ( coherence-square-cocone-span s c x)
                    ( h (left-map-span s x)))
                ( h' ∘ right-map-span s))))
```
