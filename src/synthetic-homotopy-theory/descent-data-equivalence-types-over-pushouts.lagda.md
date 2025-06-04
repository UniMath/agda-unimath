# Descent data for type families of equivalence types over pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts where
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
`R ≈ (RA, RB, RS)`, we show that
[fiberwise equivalences](foundation-core.families-of-equivalences.md)
`(x : X) → P x ≃ R x` correspond to
[equivalences](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md)
`(PA, PB, PS) ≃ (RA, RB, RS)`.

**Proof:** The proof follows exactly the same pattern as the one in
[`descent-data-function-types-over-pushouts`](synthetic-homotopy-theory.descent-data-function-types-over-pushouts.md).

## Definitions

### The type family of fiberwise equivalences with corresponding descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (R : family-with-descent-data-pushout c l8 l9 l10)
  where

  family-cocone-equivalence-type-pushout : X → UU (l7 ⊔ l10)
  family-cocone-equivalence-type-pushout x =
    family-cocone-family-with-descent-data-pushout P x ≃
    family-cocone-family-with-descent-data-pushout R x

  descent-data-equivalence-type-pushout :
    descent-data-pushout 𝒮 (l5 ⊔ l8) (l6 ⊔ l9)
  pr1 descent-data-equivalence-type-pushout a =
    left-family-family-with-descent-data-pushout P a ≃
    left-family-family-with-descent-data-pushout R a
  pr1 (pr2 descent-data-equivalence-type-pushout) b =
    right-family-family-with-descent-data-pushout P b ≃
    right-family-family-with-descent-data-pushout R b
  pr2 (pr2 descent-data-equivalence-type-pushout) s =
    ( equiv-postcomp-equiv
      ( equiv-family-family-with-descent-data-pushout R s)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (equiv-family-family-with-descent-data-pushout P s))
      ( _))

  left-equiv-equiv-descent-data-equivalence-type-pushout :
    (a : domain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( horizontal-map-cocone _ _ c a) ≃
      family-cocone-family-with-descent-data-pushout R
        ( horizontal-map-cocone _ _ c a)) ≃
    ( left-family-family-with-descent-data-pushout P a ≃
      left-family-family-with-descent-data-pushout R a)
  left-equiv-equiv-descent-data-equivalence-type-pushout a =
    ( equiv-postcomp-equiv
      ( left-equiv-family-with-descent-data-pushout R a)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (left-equiv-family-with-descent-data-pushout P a))
      ( _))

  right-equiv-equiv-descent-data-equivalence-type-pushout :
    (b : codomain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( vertical-map-cocone _ _ c b) ≃
      family-cocone-family-with-descent-data-pushout R
        ( vertical-map-cocone _ _ c b)) ≃
    ( right-family-family-with-descent-data-pushout P b ≃
      right-family-family-with-descent-data-pushout R b)
  right-equiv-equiv-descent-data-equivalence-type-pushout b =
    ( equiv-postcomp-equiv
      ( right-equiv-family-with-descent-data-pushout R b)
      ( _)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (right-equiv-family-with-descent-data-pushout P b))
      ( _))

  coherence-equiv-descent-data-equivalence-type-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv
        ( left-equiv-equiv-descent-data-equivalence-type-pushout
          ( left-map-span-diagram 𝒮 s)))
      ( tr
        ( family-cocone-equivalence-type-pushout)
        ( coherence-square-cocone _ _ c s))
      ( map-family-descent-data-pushout
        ( descent-data-equivalence-type-pushout)
        ( s))
      ( map-equiv
        ( right-equiv-equiv-descent-data-equivalence-type-pushout
          ( right-map-span-diagram 𝒮 s)))
  coherence-equiv-descent-data-equivalence-type-pushout s =
    ( ( map-equiv
      ( right-equiv-equiv-descent-data-equivalence-type-pushout
        ( right-map-span-diagram 𝒮 s))) ·l
      ( tr-equiv-type
        ( family-cocone-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout R)
        ( coherence-square-cocone _ _ c s))) ∙h
    ( λ e →
      eq-htpy-equiv
        ( horizontal-concat-htpy
          ( coherence-family-with-descent-data-pushout R s ·r map-equiv e)
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

  equiv-descent-data-equivalence-type-pushout :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-equivalence-type-pushout))
      ( descent-data-equivalence-type-pushout)
  pr1 equiv-descent-data-equivalence-type-pushout =
    left-equiv-equiv-descent-data-equivalence-type-pushout
  pr1 (pr2 equiv-descent-data-equivalence-type-pushout) =
    right-equiv-equiv-descent-data-equivalence-type-pushout
  pr2 (pr2 equiv-descent-data-equivalence-type-pushout) =
    coherence-equiv-descent-data-equivalence-type-pushout

  family-with-descent-data-equivalence-type-pushout :
    family-with-descent-data-pushout c (l5 ⊔ l8) (l6 ⊔ l9) (l7 ⊔ l10)
  pr1 family-with-descent-data-equivalence-type-pushout =
    family-cocone-equivalence-type-pushout
  pr1 (pr2 family-with-descent-data-equivalence-type-pushout) =
    descent-data-equivalence-type-pushout
  pr2 (pr2 family-with-descent-data-equivalence-type-pushout) =
    equiv-descent-data-equivalence-type-pushout
```

## Properties

### Sections of descent data for families of equivalences correspond to equivalences of descent data

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (R : family-with-descent-data-pushout c l8 l9 l10)
  where

  equiv-section-descent-data-equivalence-type-pushout :
    section-descent-data-pushout
      ( descent-data-equivalence-type-pushout P R) →
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  equiv-section-descent-data-equivalence-type-pushout =
    tot
      ( λ tA →
        tot
          ( λ tB tS s →
            inv-htpy
              ( map-inv-equiv
                ( equiv-coherence-triangle-maps-inv-top'
                  ( ( map-family-family-with-descent-data-pushout R s) ∘
                    ( map-equiv (tA (left-map-span-diagram 𝒮 s))))
                  ( map-equiv (tB (right-map-span-diagram 𝒮 s)))
                  ( equiv-family-family-with-descent-data-pushout P s))
                ( htpy-eq-equiv (tS s)))))

  abstract
    is-equiv-equiv-section-descent-data-equivalence-type-pushout :
      is-equiv equiv-section-descent-data-equivalence-type-pushout
    is-equiv-equiv-section-descent-data-equivalence-type-pushout =
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
                          ( (map-family-family-with-descent-data-pushout R s) ∘
                            ( map-equiv (tA (left-map-span-diagram 𝒮 s))))
                          ( map-equiv (tB (right-map-span-diagram 𝒮 s)))
                          ( equiv-family-family-with-descent-data-pushout P s)))
                      ( is-equiv-inv-htpy _ _)))))

  equiv-descent-data-equiv-family-cocone-span-diagram :
    ( (x : X) →
      family-cocone-family-with-descent-data-pushout P x ≃
      family-cocone-family-with-descent-data-pushout R x) →
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  equiv-descent-data-equiv-family-cocone-span-diagram =
    ( equiv-section-descent-data-equivalence-type-pushout) ∘
    ( section-descent-data-section-family-cocone-span-diagram
      ( family-with-descent-data-equivalence-type-pushout P R))

  abstract
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv equiv-descent-data-equiv-family-cocone-span-diagram
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram up-c =
      is-equiv-comp _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagram _
          ( up-c))
        ( is-equiv-equiv-section-descent-data-equivalence-type-pushout)
```

As a corollary, given an equivalence
`(hA, hB, hS) : (PA, PB, PS) ≃ (RA, RB, RS)`, there is a unique family of
equivalences `h : (x : X) → P x → R x` such that its induced equivalence is
homotopic to `(hA, hB, hS)`. The homotopy provides us in particular with the
component-wise [homotopies](foundation-core.homotopies.md)

```text
                 hA a                               hB a
          PA a --------> RA a                PB b --------> RB b
            |              ∧                   |              ∧
  (eᴾA a)⁻¹ |              | eᴿA a   (eᴾB b)⁻¹ |              | eᴿB b
            |              |                   |              |
            ∨              |                   ∨              |
         P (ia) ------> R (ia)              P (jb) ------> R (jb)
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
      R (ia) -------> RA a            R (jb) -------> RB b
              eᴿA a                           eᴿB b
```

by inverting the inverted equivalences.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (R : family-with-descent-data-pushout c l8 l9 l10)
  (e :
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R))
  where

  abstract
    uniqueness-equiv-equiv-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) →
              family-cocone-family-with-descent-data-pushout P x ≃
              family-cocone-family-with-descent-data-pushout R x)
            ( λ h →
              htpy-equiv-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( descent-data-family-with-descent-data-pushout R)
                ( equiv-descent-data-equiv-family-cocone-span-diagram P R h)
                ( e)))
    uniqueness-equiv-equiv-descent-data-pushout =
      is-contr-equiv'
        ( fiber (equiv-descent-data-equiv-family-cocone-span-diagram P R) e)
        ( equiv-tot
          ( λ f → extensionality-equiv-descent-data-pushout _ e))
        ( is-contr-map-is-equiv
          ( is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram P R
            ( up-c))
          ( e))

  equiv-equiv-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x ≃
    family-cocone-family-with-descent-data-pushout R x
  equiv-equiv-descent-data-pushout =
    pr1 (center uniqueness-equiv-equiv-descent-data-pushout)

  map-equiv-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout R x
  map-equiv-descent-data-pushout x =
    map-equiv (equiv-equiv-descent-data-pushout x)

  compute-left-map-equiv-equiv-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    coherence-square-maps
      ( left-map-family-with-descent-data-pushout P a)
      ( map-equiv-descent-data-pushout (horizontal-map-cocone _ _ c a))
      ( left-map-equiv-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout R)
        ( e)
        ( a))
      ( left-map-family-with-descent-data-pushout R a)
  compute-left-map-equiv-equiv-descent-data-pushout a =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( left-map-family-with-descent-data-pushout R a ∘
          map-equiv-descent-data-pushout (horizontal-map-cocone _ _ c a))
        ( left-map-equiv-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
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
        ( descent-data-family-with-descent-data-pushout R)
        ( e)
        ( b))
      ( right-map-family-with-descent-data-pushout R b)
  compute-right-map-equiv-equiv-descent-data-pushout b =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( right-map-family-with-descent-data-pushout R b ∘
          map-equiv-descent-data-pushout (vertical-map-cocone _ _ c b))
        ( right-map-equiv-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
          ( e)
          ( b))
        ( right-equiv-family-with-descent-data-pushout P b))
      ( pr1 (pr2 (pr2 (center uniqueness-equiv-equiv-descent-data-pushout))) b)
```
