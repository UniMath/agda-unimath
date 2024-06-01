# Descent data for families of equivalences over pushouts

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.descent-data-pushouts-equivalence-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.postcomposition-functions
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Given two
[families with descent data](synthetic-homotopy-theory.families-descent-data-pushouts.md)
for [pushouts](synthetic-homotopy-theory.pushouts.md) `P ≈ (PA, PB, PS)` and
`Q ≈ (QA, QB, QS)`, we show that fiberwise equivalences `(x : X) → P x ≃ Q x`
correspond to
[equivalences](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md)
`(PA, PB, PS) ≃ (QA, QB, QS)`.

**Proof:** The proof follows exactly the same pattern as the one in
[`descent-data-pushouts-function-families`](synthetic-homotopy-theory.descent-data-pushouts-function-families.md).

## Definitions

### The type family of fiberwise equivalences with corresponding descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  (Q : family-with-descent-data-pushout c l6)
  where

  family-cocone-family-with-descent-data-pushout-equivalence-family :
    X → UU (l5 ⊔ l6)
  family-cocone-family-with-descent-data-pushout-equivalence-family x =
    family-cocone-family-with-descent-data-pushout P x ≃
    family-cocone-family-with-descent-data-pushout Q x

  descent-data-pushout-equivalence-family :
    descent-data-pushout 𝒮 (l5 ⊔ l6)
  pr1 descent-data-pushout-equivalence-family a =
    left-family-family-with-descent-data-pushout P a ≃
    left-family-family-with-descent-data-pushout Q a
  pr1 (pr2 descent-data-pushout-equivalence-family) b =
    right-family-family-with-descent-data-pushout P b ≃
    right-family-family-with-descent-data-pushout Q b
  pr2 (pr2 descent-data-pushout-equivalence-family) s =
    ( equiv-postcomp-equiv
      ( equiv-family-family-with-descent-data-pushout Q s)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (equiv-family-family-with-descent-data-pushout P s))
      ( _))

  left-equiv-equiv-descent-data-pushout-equivalence-family :
    (a : domain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( horizontal-map-cocone _ _ c a) ≃
      family-cocone-family-with-descent-data-pushout Q
        ( horizontal-map-cocone _ _ c a)) ≃
    ( left-family-family-with-descent-data-pushout P a ≃
      left-family-family-with-descent-data-pushout Q a)
  left-equiv-equiv-descent-data-pushout-equivalence-family a =
    ( equiv-postcomp-equiv
      ( left-equiv-family-with-descent-data-pushout Q a)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (left-equiv-family-with-descent-data-pushout P a))
      ( _))

  right-equiv-equiv-descent-data-pushout-equivalence-family :
    (b : codomain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( vertical-map-cocone _ _ c b) ≃
      family-cocone-family-with-descent-data-pushout Q
        ( vertical-map-cocone _ _ c b)) ≃
    ( right-family-family-with-descent-data-pushout P b ≃
      right-family-family-with-descent-data-pushout Q b)
  right-equiv-equiv-descent-data-pushout-equivalence-family b =
    ( equiv-postcomp-equiv
      ( right-equiv-family-with-descent-data-pushout Q b)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (right-equiv-family-with-descent-data-pushout P b))
      ( _))

  coherence-equiv-descent-data-pushout-equivalence-family :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv
        ( left-equiv-equiv-descent-data-pushout-equivalence-family
          ( left-map-span-diagram 𝒮 s)))
      ( tr
        ( family-cocone-family-with-descent-data-pushout-equivalence-family)
        ( coherence-square-cocone _ _ c s))
      ( map-family-descent-data-pushout
        ( descent-data-pushout-equivalence-family)
        ( s))
      ( map-equiv
        ( right-equiv-equiv-descent-data-pushout-equivalence-family
          ( right-map-span-diagram 𝒮 s)))
  coherence-equiv-descent-data-pushout-equivalence-family s =
    ( ( map-equiv
      ( right-equiv-equiv-descent-data-pushout-equivalence-family
        ( right-map-span-diagram 𝒮 s))) ·l
      ( tr-equiv-type
        ( family-cocone-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout Q)
        ( coherence-square-cocone _ _ c s))) ∙h
    ( λ e →
      eq-htpy-equiv
        ( horizontal-concat-htpy
          ( coherence-family-with-descent-data-pushout Q s ·r map-equiv e)
          ( coherence-square-maps-inv-equiv
            ( equiv-tr
              ( family-cocone-family-with-descent-data-pushout P)
              ( coherence-square-cocone _ _ c s))
            ( left-equiv-family-with-descent-data-pushout P
              ( left-map-span-diagram 𝒮 s))
            ( right-equiv-family-with-descent-data-pushout P
              ( right-map-span-diagram 𝒮 s))
            ( equiv-family-family-with-descent-data-pushout P s)
            ( inv-htpy (coherence-family-with-descent-data-pushout P s)))))

  equiv-descent-data-pushout-equivalence-family :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout-equivalence-family))
      ( descent-data-pushout-equivalence-family)
  pr1 equiv-descent-data-pushout-equivalence-family =
    left-equiv-equiv-descent-data-pushout-equivalence-family
  pr1 (pr2 equiv-descent-data-pushout-equivalence-family) =
    right-equiv-equiv-descent-data-pushout-equivalence-family
  pr2 (pr2 equiv-descent-data-pushout-equivalence-family) =
    coherence-equiv-descent-data-pushout-equivalence-family

  family-with-descent-data-pushout-equivalence-family :
    family-with-descent-data-pushout c (l5 ⊔ l6)
  pr1 family-with-descent-data-pushout-equivalence-family =
    family-cocone-family-with-descent-data-pushout-equivalence-family
  pr1 (pr2 family-with-descent-data-pushout-equivalence-family) =
    descent-data-pushout-equivalence-family
  pr2 (pr2 family-with-descent-data-pushout-equivalence-family) =
    equiv-descent-data-pushout-equivalence-family
```

## Properties

### Sections of descent data for families of equivalences correspond to equivalences of descent data

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  (Q : family-with-descent-data-pushout c l6)
  where

  equiv-section-descent-data-pushout-equivalence-family :
    section-descent-data-pushout
      ( descent-data-pushout-equivalence-family P Q) →
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout Q)
  pr1 (equiv-section-descent-data-pushout-equivalence-family t) =
    left-map-section-descent-data-pushout
      ( descent-data-pushout-equivalence-family P Q)
      ( t)
  pr1 (pr2 (equiv-section-descent-data-pushout-equivalence-family t)) =
    right-map-section-descent-data-pushout
      ( descent-data-pushout-equivalence-family P Q)
      ( t)
  pr2 (pr2 (equiv-section-descent-data-pushout-equivalence-family t)) s =
    inv-htpy
      ( map-inv-equiv
        ( equiv-coherence-triangle-maps-inv-top'
          ( ( map-family-family-with-descent-data-pushout Q s) ∘
            ( map-equiv
              ( left-map-section-descent-data-pushout
                ( descent-data-pushout-equivalence-family P Q)
                ( t)
                ( left-map-span-diagram 𝒮 s))))
          ( map-equiv
            ( right-map-section-descent-data-pushout
              ( descent-data-pushout-equivalence-family P Q)
              ( t)
              ( right-map-span-diagram 𝒮 s)))
          ( equiv-family-family-with-descent-data-pushout P s))
        ( htpy-eq-equiv
          ( coherence-section-descent-data-pushout
            ( descent-data-pushout-equivalence-family P Q)
            ( t)
            ( s))))

  abstract
    is-equiv-equiv-section-descent-data-pushout-equivalence-family :
      is-equiv equiv-section-descent-data-pushout-equivalence-family
    is-equiv-equiv-section-descent-data-pushout-equivalence-family =
      is-equiv-tot-is-fiberwise-equiv
        ( λ tA →
          is-equiv-tot-is-fiberwise-equiv
            ( λ tB →
              is-equiv-map-Π-is-fiberwise-equiv
                ( λ s →
                  is-equiv-comp _ _
                    ( is-equiv-map-equiv (extensionality-equiv _ _))
                    ( is-equiv-comp _ _
                      ( is-equiv-map-inv-equiv
                        ( equiv-coherence-triangle-maps-inv-top'
                          ( (map-family-family-with-descent-data-pushout Q s) ∘
                            ( map-equiv (tA (left-map-span-diagram 𝒮 s))))
                          ( map-equiv (tB (right-map-span-diagram 𝒮 s)))
                          ( equiv-family-family-with-descent-data-pushout P s)))
                      ( is-equiv-inv-htpy _ _)))))

  equiv-descent-data-equiv-family-cocone-span-diagram :
    ( (x : X) →
      family-cocone-family-with-descent-data-pushout P x ≃
      family-cocone-family-with-descent-data-pushout Q x) →
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout Q)
  equiv-descent-data-equiv-family-cocone-span-diagram =
    ( equiv-section-descent-data-pushout-equivalence-family) ∘
    ( section-descent-data-section-family-cocone-span-diagram
      ( family-with-descent-data-pushout-equivalence-family P Q))

  abstract
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv equiv-descent-data-equiv-family-cocone-span-diagram
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram up-c =
      is-equiv-comp _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagram _
          ( up-c))
        ( is-equiv-equiv-section-descent-data-pushout-equivalence-family)
```

As a corollary, given an equivalence
`(hA, hB, hS) : (PA, PB, PS) ≃ (QA, QB, QS)`, there is a unique family of
equivalences `h : (x : X) → P x → Q x` such that its induced equivalence is
homotopic to `(hA, hB, hS)`. The homotopy provides us in particular with the
component-wise [homotopies](foundation-core.homotopies.md)

```text
                 hA a                               hB a
          PA a --------> QA a                PB b --------> QB b
            |              ∧                   |              ∧
  (eᴾA a)⁻¹ |              | eꟴA a   (eᴾB b)⁻¹ |              | eꟴB b
            |              |                   |              |
            ∨              |                   ∨              |
         P (ia) ------> Q (ia)              P (jb) ------> Q (jb)
                h (ia)                             h (jb)
```

which we can turn into the computation rules

```text
              eᴾA a                           eᴾB a
      P (ia) -------> PA a            P (jb) -------> PB b
         |              |                |              |
  h (ia) |              | hA a    h (jb) |              | hB b
         |              |                |              |
         ∨              ∨                ∨              ∨
      Q (ia) -------> QA a            Q (jb) -------> QB b
              eꟴA a                           eꟴB b
```

by inverting the inverted equivalences.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : family-with-descent-data-pushout c l5)
  (Q : family-with-descent-data-pushout c l6)
  (e :
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout Q))
  where

  abstract
    uniqueness-equiv-equiv-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) →
              family-cocone-family-with-descent-data-pushout P x ≃
              family-cocone-family-with-descent-data-pushout Q x)
            ( λ h →
              htpy-equiv-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( descent-data-family-with-descent-data-pushout Q)
                ( equiv-descent-data-equiv-family-cocone-span-diagram P Q h)
                ( e)))
    uniqueness-equiv-equiv-descent-data-pushout =
      is-contr-equiv'
        ( fiber (equiv-descent-data-equiv-family-cocone-span-diagram P Q) e)
        ( equiv-tot
          ( λ f → extensionality-equiv-descent-data-pushout _ e))
        ( is-contr-map-is-equiv
          ( is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram P Q
            ( up-c))
          ( e))

  equiv-equiv-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x ≃
    family-cocone-family-with-descent-data-pushout Q x
  equiv-equiv-descent-data-pushout =
    pr1 (center uniqueness-equiv-equiv-descent-data-pushout)

  map-equiv-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout Q x
  map-equiv-descent-data-pushout x =
    map-equiv (equiv-equiv-descent-data-pushout x)

  compute-left-map-equiv-equiv-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    coherence-square-maps
      ( left-map-family-with-descent-data-pushout P a)
      ( map-equiv-descent-data-pushout (horizontal-map-cocone _ _ c a))
      ( left-map-equiv-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout Q)
        ( e)
        ( a))
      ( left-map-family-with-descent-data-pushout Q a)
  compute-left-map-equiv-equiv-descent-data-pushout a =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( left-map-family-with-descent-data-pushout Q a ∘
          map-equiv-descent-data-pushout (horizontal-map-cocone _ _ c a))
        ( left-map-equiv-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout Q)
          ( e)
          ( a))
        ( left-equiv-family-with-descent-data-pushout P a))
      ( pr1 (pr2 (center uniqueness-equiv-equiv-descent-data-pushout)) a)

  compute-right-map-equiv-equiv-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    coherence-square-maps
      ( right-map-family-with-descent-data-pushout P b)
      ( map-equiv-descent-data-pushout (vertical-map-cocone _ _ c b))
      ( right-map-equiv-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout Q)
        ( e)
        ( b))
      ( right-map-family-with-descent-data-pushout Q b)
  compute-right-map-equiv-equiv-descent-data-pushout b =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( right-map-family-with-descent-data-pushout Q b ∘
          map-equiv-descent-data-pushout (vertical-map-cocone _ _ c b))
        ( right-map-equiv-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout Q)
          ( e)
          ( b))
        ( right-equiv-family-with-descent-data-pushout P b))
      ( pr1 (pr2 (pr2 (center uniqueness-equiv-equiv-descent-data-pushout))) b)
```
