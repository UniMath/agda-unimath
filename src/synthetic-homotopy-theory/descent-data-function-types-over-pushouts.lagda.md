# Descent data for type families of function types over pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.descent-data-function-types-over-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
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
[fiberwise maps](foundation.families-of-maps.md) `(x : X) → P x → R x`
correspond to
[morphisms](synthetic-homotopy-theory.morphisms-descent-data-pushouts.md)
`(PA, PB, PS) → (RA, RB, RS)`.

**Proof:** We first characterize the type family `x ↦ (P x → R x)`. The
corresponding [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
consists of the type families

```text
  a ↦ (PA a → RA a)
  b ↦ (PB b → RB b),
```

and the gluing data sending `h : PA (fs) → RA (fs)` to
`(RS s ∘ h ∘ (PS s)⁻¹) : PB (gs) → RB (gs)`.

**Note:** It is important to differentiate between families of _function types_,
i.e. a type family that to every `x : X` assigns the _type_ `P x → R x`, and
families of _functions_, i.e. a family that to every `x : X` assigns a
_function_ from `P x` to `R x`. Descent data plays the role of a family of
types, so it makes sense to talk about "descent data corresponding to a family
of function types", but it doesn't make sense to talk about "descent data
corresponding to a family of functions". The kind of data that corresponds to
families of functions are the _sections_ of the descent data of a family of
function types.

It suffices to show that the sections correspond to morphisms. The first two
components of a section and a morphism agree, namely they are

```text
  sA : (a : A) → PA a → RA a
  sB : (b : B) → PB b → RB b,
```

respectively. The coherence datum of a section has the type

```text
  (s : S) → RS s ∘ sA (fs) ∘ (RS s)⁻¹ = sB (gs),
```

which we can massage into a coherence of the morphism as

```text
  RS s ∘ sA (fs) ∘ (PS s)⁻¹ = sB (gs)
  ≃ RS s ∘ sA (fs) ∘ (PS s)⁻¹ ~ sB (gs)  by function extensionality
  ≃ RS s ∘ sA (fs) ~ sB (gs) ∘ PS s      by transposition of (PS s)
  ≃ sB (gs) ∘ PS s ~ RS s ∘ sA (fs)      by symmetry of homotopies.
```

## Definitions

### The type family of fiberwise functions with corresponding descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (R : family-with-descent-data-pushout c l8 l9 l10)
  where

  family-cocone-function-type-pushout : X → UU (l7 ⊔ l10)
  family-cocone-function-type-pushout x =
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout R x

  descent-data-function-type-pushout :
    descent-data-pushout 𝒮 (l5 ⊔ l8) (l6 ⊔ l9)
  pr1 descent-data-function-type-pushout a =
    left-family-family-with-descent-data-pushout P a →
    left-family-family-with-descent-data-pushout R a
  pr1 (pr2 descent-data-function-type-pushout) b =
    right-family-family-with-descent-data-pushout P b →
    right-family-family-with-descent-data-pushout R b
  pr2 (pr2 descent-data-function-type-pushout) s =
    ( equiv-postcomp _
      ( equiv-family-family-with-descent-data-pushout R s)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-family-with-descent-data-pushout P s))
      ( _))

  left-equiv-equiv-descent-data-function-type-pushout :
    (a : domain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( horizontal-map-cocone _ _ c a) →
      family-cocone-family-with-descent-data-pushout R
        ( horizontal-map-cocone _ _ c a)) ≃
    ( left-family-family-with-descent-data-pushout P a →
      left-family-family-with-descent-data-pushout R a)
  left-equiv-equiv-descent-data-function-type-pushout a =
    ( equiv-postcomp _
      ( left-equiv-family-with-descent-data-pushout R a)) ∘e
    ( equiv-precomp
      ( inv-equiv (left-equiv-family-with-descent-data-pushout P a))
      ( _))

  right-equiv-equiv-descent-data-function-type-pushout :
    (b : codomain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( vertical-map-cocone _ _ c b) →
      family-cocone-family-with-descent-data-pushout R
        ( vertical-map-cocone _ _ c b)) ≃
    ( right-family-family-with-descent-data-pushout P b →
      right-family-family-with-descent-data-pushout R b)
  right-equiv-equiv-descent-data-function-type-pushout b =
    ( equiv-postcomp _
      ( right-equiv-family-with-descent-data-pushout R b)) ∘e
    ( equiv-precomp
      ( inv-equiv (right-equiv-family-with-descent-data-pushout P b))
      ( _))

  coherence-equiv-descent-data-function-type-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv
        ( left-equiv-equiv-descent-data-function-type-pushout
          ( left-map-span-diagram 𝒮 s)))
      ( tr
        ( family-cocone-function-type-pushout)
        ( coherence-square-cocone _ _ c s))
      ( map-family-descent-data-pushout
        ( descent-data-function-type-pushout)
        ( s))
      ( map-equiv
        ( right-equiv-equiv-descent-data-function-type-pushout
          ( right-map-span-diagram 𝒮 s)))
  coherence-equiv-descent-data-function-type-pushout s =
    ( ( map-equiv
        ( right-equiv-equiv-descent-data-function-type-pushout
          ( right-map-span-diagram 𝒮 s))) ·l
      ( tr-function-type
        ( family-cocone-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout R)
        ( coherence-square-cocone _ _ c s))) ∙h
    ( λ h →
      eq-htpy
        ( horizontal-concat-htpy
          ( coherence-family-with-descent-data-pushout R s ·r h)
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

  equiv-descent-data-function-type-pushout :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-function-type-pushout))
      ( descent-data-function-type-pushout)
  pr1 equiv-descent-data-function-type-pushout =
    left-equiv-equiv-descent-data-function-type-pushout
  pr1 (pr2 equiv-descent-data-function-type-pushout) =
    right-equiv-equiv-descent-data-function-type-pushout
  pr2 (pr2 equiv-descent-data-function-type-pushout) =
    coherence-equiv-descent-data-function-type-pushout

  family-with-descent-data-function-type-pushout :
    family-with-descent-data-pushout c (l5 ⊔ l8) (l6 ⊔ l9) (l7 ⊔ l10)
  pr1 family-with-descent-data-function-type-pushout =
    family-cocone-function-type-pushout
  pr1 (pr2 family-with-descent-data-function-type-pushout) =
    descent-data-function-type-pushout
  pr2 (pr2 family-with-descent-data-function-type-pushout) =
    equiv-descent-data-function-type-pushout
```

## Properties

### Sections of descent data for families of functions correspond to morphisms of descent data

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (R : family-with-descent-data-pushout c l8 l9 l10)
  where

  hom-section-descent-data-function-type-pushout :
    section-descent-data-pushout (descent-data-function-type-pushout P R) →
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  hom-section-descent-data-function-type-pushout =
    tot
      ( λ tA →
        tot
        ( λ tB tS s →
          inv-htpy
            ( map-inv-equiv
              ( equiv-coherence-triangle-maps-inv-top'
                ( ( map-family-family-with-descent-data-pushout R s) ∘
                  ( tA (left-map-span-diagram 𝒮 s)))
                ( tB (right-map-span-diagram 𝒮 s))
                ( equiv-family-family-with-descent-data-pushout P s))
              ( htpy-eq (tS s)))))

  abstract
    is-equiv-hom-section-descent-data-function-type-pushout :
      is-equiv hom-section-descent-data-function-type-pushout
    is-equiv-hom-section-descent-data-function-type-pushout =
      is-equiv-tot-is-fiberwise-equiv
        ( λ tA →
          is-equiv-tot-is-fiberwise-equiv
            ( λ tB →
              is-equiv-map-Π-is-fiberwise-equiv
                ( λ s →
                  is-equiv-comp _ _
                    ( funext _ _)
                    ( is-equiv-comp _ _
                      ( is-equiv-map-inv-equiv
                        ( equiv-coherence-triangle-maps-inv-top'
                          ( ( map-family-family-with-descent-data-pushout R s) ∘
                            ( tA (left-map-span-diagram 𝒮 s)))
                          ( tB (right-map-span-diagram 𝒮 s))
                          ( equiv-family-family-with-descent-data-pushout P s)))
                      ( is-equiv-inv-htpy _ _)))))

  hom-descent-data-map-family-cocone-span-diagram :
    ( (x : X) →
      family-cocone-family-with-descent-data-pushout P x →
      family-cocone-family-with-descent-data-pushout R x) →
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  hom-descent-data-map-family-cocone-span-diagram =
    ( hom-section-descent-data-function-type-pushout) ∘
    ( section-descent-data-section-family-cocone-span-diagram
      ( family-with-descent-data-function-type-pushout P R))

  abstract
    is-equiv-hom-descent-data-map-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv hom-descent-data-map-family-cocone-span-diagram
    is-equiv-hom-descent-data-map-family-cocone-span-diagram up-c =
      is-equiv-comp _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagram _
          ( up-c))
        ( is-equiv-hom-section-descent-data-function-type-pushout)
```

As a corollary, given a morphism `(hA, hB, hS) : (PA, PB, PS) → (RA, RB, RS)`,
there is a unique family of maps `h : (x : X) → P x → R x` such that its induced
morphism is homotopic to `(hA, hB, hS)`. The homotopy provides us in particular
with the component-wise [homotopies](foundation-core.homotopies.md)

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
  (m :
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R))
  where

  abstract
    uniqueness-map-hom-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) →
              family-cocone-family-with-descent-data-pushout P x →
              family-cocone-family-with-descent-data-pushout R x)
            ( λ h →
              htpy-hom-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( descent-data-family-with-descent-data-pushout R)
                ( hom-descent-data-map-family-cocone-span-diagram P R h)
                ( m)))
    uniqueness-map-hom-descent-data-pushout =
      is-contr-equiv'
        ( fiber (hom-descent-data-map-family-cocone-span-diagram P R) m)
        ( equiv-tot
          ( λ h → extensionality-hom-descent-data-pushout _ _ _ m))
        ( is-contr-map-is-equiv
          ( is-equiv-hom-descent-data-map-family-cocone-span-diagram P R up-c)
          ( m))

  map-hom-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout R x
  map-hom-descent-data-pushout =
    pr1 (center uniqueness-map-hom-descent-data-pushout)

  compute-left-map-map-hom-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    coherence-square-maps
      ( left-map-family-with-descent-data-pushout P a)
      ( map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
      ( left-map-hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout R)
        ( m)
        ( a))
      ( left-map-family-with-descent-data-pushout R a)
  compute-left-map-map-hom-descent-data-pushout a =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( left-map-family-with-descent-data-pushout R a ∘
          map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
        ( left-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
          ( m)
          ( a))
        ( left-equiv-family-with-descent-data-pushout P a))
      ( pr1 (pr2 (center uniqueness-map-hom-descent-data-pushout)) a)

  compute-right-map-map-hom-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    coherence-square-maps
      ( right-map-family-with-descent-data-pushout P b)
      ( map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
      ( right-map-hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout R)
        ( m)
        ( b))
      ( right-map-family-with-descent-data-pushout R b)
  compute-right-map-map-hom-descent-data-pushout b =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( right-map-family-with-descent-data-pushout R b ∘
          map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
        ( right-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
          ( m)
          ( b))
        ( right-equiv-family-with-descent-data-pushout P b))
      ( pr1 (pr2 (pr2 (center uniqueness-map-hom-descent-data-pushout))) b)
```
