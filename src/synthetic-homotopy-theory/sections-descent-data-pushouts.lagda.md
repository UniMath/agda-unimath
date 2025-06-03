# Sections of descent data for pushouts

```agda
module synthetic-homotopy-theory.sections-descent-data-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Given [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
`(PA, PB, PS)` for the [pushout](synthetic-homotopy-theory.pushouts.md) of a
[span diagram](foundation.span-diagrams.md) `𝒮`, we define the type of
{{#concept "sections" Disambiguation="descent data for pushouts" Agda=section-descent-data-pushout}}
to be the type of triples `(tA, tB, tS)`, where

```text
  tA : (a : A) → PA a
  tB : (b : B) → PB b
```

are [sections](foundation.dependent-function-types.md) of the type families `PA`
and `PB`, respectively, and `tS` is a coherence datum, witnessing that for every
`s : S`, the dependent triangle

```text
           tA ∘ f
  (s : S) --------> PA (f s)
          \       /
    tB ∘ g  \   / PS s
             ∨ ∨
          PB (g s)
```

[commutes](foundation.commuting-triangles-of-maps.md).

We show that for a
[family with descent data](synthetic-homotopy-theory.families-descent-data-pushouts.md)
`P ≈ (PA, PB, PS)`, the type of sections `(x : X) → P x` of `P` is
[equivalent](foundation-core.equivalences.md) to the type of sections of
`(PA, PB, PS)`.

Furthermore, a
{{#concept "homotopy" Disambiguation="sections of descent data for pushouts" Agda=htpy-section-descent-data-pushout}}
between sections `(tA, tB, tS)` and `(rA, rB, rS)` consists of component-wise
[homotopies](foundation-core.homotopies.md)

```text
  HA : tA ~ rA
  HB : tB ~ rB
```

and a coherence datum `HS`, witnessing that for each `s : S`, the square of
identifications

```text
               PS s ·l HA fs
  PS s (tA fs) ------------> PS s (rA fs)
       |                          |
  tS s |                          | rS s
       |                          |
       ∨                          ∨
     tB gs -------------------> rB gs
                   HB gs
```

[commutes](foundation-core.commuting-squares-of-identifications.md).

We show that the identity types of sections of descent data are characterized by
homotopies between them.

## Definitions

### Sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  section-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  section-descent-data-pushout =
    Σ ( (a : domain-span-diagram 𝒮) → left-family-descent-data-pushout P a)
      ( λ tA →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-family-descent-data-pushout P b)
          ( λ tB →
            (s : spanning-type-span-diagram 𝒮) →
            map-family-descent-data-pushout P s
              ( tA (left-map-span-diagram 𝒮 s)) ＝
            tB (right-map-span-diagram 𝒮 s)))

  module _
    (t : section-descent-data-pushout)
    where

    left-map-section-descent-data-pushout :
      (a : domain-span-diagram 𝒮) → left-family-descent-data-pushout P a
    left-map-section-descent-data-pushout = pr1 t

    right-map-section-descent-data-pushout :
      (b : codomain-span-diagram 𝒮) → right-family-descent-data-pushout P b
    right-map-section-descent-data-pushout = pr1 (pr2 t)

    coherence-section-descent-data-pushout :
      (s : spanning-type-span-diagram 𝒮) →
      map-family-descent-data-pushout P s
        ( left-map-section-descent-data-pushout (left-map-span-diagram 𝒮 s)) ＝
      right-map-section-descent-data-pushout (right-map-span-diagram 𝒮 s)
    coherence-section-descent-data-pushout = pr2 (pr2 t)
```

### Homotopies of sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (r t : section-descent-data-pushout P)
  where

  htpy-section-descent-data-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  htpy-section-descent-data-pushout =
    Σ ( left-map-section-descent-data-pushout P r ~
        left-map-section-descent-data-pushout P t)
      ( λ HA →
        Σ ( right-map-section-descent-data-pushout P r ~
            right-map-section-descent-data-pushout P t)
          ( λ HB →
            (s : spanning-type-span-diagram 𝒮) →
            coherence-square-identifications
              ( ap
                ( map-family-descent-data-pushout P s)
                ( HA (left-map-span-diagram 𝒮 s)))
              ( coherence-section-descent-data-pushout P r s)
              ( coherence-section-descent-data-pushout P t s)
              ( HB (right-map-span-diagram 𝒮 s))))
```

### The reflexive homotopy of sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (r : section-descent-data-pushout P)
  where

  refl-htpy-section-descent-data-pushout :
    htpy-section-descent-data-pushout P r r
  pr1 refl-htpy-section-descent-data-pushout = refl-htpy
  pr1 (pr2 refl-htpy-section-descent-data-pushout) = refl-htpy
  pr2 (pr2 refl-htpy-section-descent-data-pushout) = right-unit-htpy
```

## Properties

### Characterization of identity types of sections of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  (r : section-descent-data-pushout P)
  where

  htpy-eq-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    (r ＝ t) → htpy-section-descent-data-pushout P r t
  htpy-eq-section-descent-data-pushout .r refl =
    refl-htpy-section-descent-data-pushout P r

  abstract
    is-torsorial-htpy-section-descent-data-pushout :
      is-torsorial (htpy-section-descent-data-pushout P r)
    is-torsorial-htpy-section-descent-data-pushout =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (left-map-section-descent-data-pushout P r))
        ( left-map-section-descent-data-pushout P r , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (right-map-section-descent-data-pushout P r))
          ( right-map-section-descent-data-pushout P r , refl-htpy)
          ( is-torsorial-htpy
            ( coherence-section-descent-data-pushout P r ∙h refl-htpy)))

  is-equiv-htpy-eq-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    is-equiv (htpy-eq-section-descent-data-pushout t)
  is-equiv-htpy-eq-section-descent-data-pushout =
    fundamental-theorem-id
      ( is-torsorial-htpy-section-descent-data-pushout)
      ( htpy-eq-section-descent-data-pushout)

  extensionality-section-descent-data-pushout :
    (t : section-descent-data-pushout P) →
    (r ＝ t) ≃ htpy-section-descent-data-pushout P r t
  pr1 (extensionality-section-descent-data-pushout t) =
    htpy-eq-section-descent-data-pushout t
  pr2 (extensionality-section-descent-data-pushout t) =
    is-equiv-htpy-eq-section-descent-data-pushout t
```

### Sections of families over a pushout correspond to sections of the corresponding descent data

**Proof:** Given a family with descent data `P ≈ (PA, PB, PS)`, note that a
section `t : (x : X) → P x` of `P` induces a section `(tA, tB, tS)` of
`(PA, PB, PS)`, where

```text
  tA a := eA (tia)
  tB b := eB (tjb),
```

and `tS s` is given by the chain of identifications

```text
  PS s (eA (tifs))
  = eB (tr P (H s) (tifs))   by coherence of P ≈ (PA, PB, PS)
  = eB (tjgs)                by apd t (H s)
```

This map factors through the dependent cocone map

```text
                dependent-cocone-map
  (x : X) → P x --------------------> dependent-cocone P
                \                  /
                  \              /
                    \          /
                      ∨      ∨
                section (PA, PB, PS),
```

where the right map takes `(dA, dB, dS)` to

```text
  tA a := eA (dA a)
  tB b := eB (dB a)
  tS s : PS s (eA (dA fs))
         = eB (tr P (H s) (dA fs))  by coherence of P ≈ (PA, PB, PS)
         = eB (dB gs)               by dS.
```

The top map is an equivalence, since we assume `X` to be a pushout, and the
right map is an equivalence, since concatenating an identification is an
equivalence, and the action on identifications of equivalences is an
equivalence. It follows that the left map is an equivalence

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  where

  section-descent-data-section-family-cocone-span-diagram :
    ((x : X) → family-cocone-family-with-descent-data-pushout P x) →
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
  pr1 (section-descent-data-section-family-cocone-span-diagram f) a =
    left-map-family-with-descent-data-pushout P a
      ( f (horizontal-map-cocone _ _ c a))
  pr1 (pr2 (section-descent-data-section-family-cocone-span-diagram f)) b =
    right-map-family-with-descent-data-pushout P b
      ( f (vertical-map-cocone _ _ c b))
  pr2 (pr2 (section-descent-data-section-family-cocone-span-diagram f)) s =
    ( inv
      ( coherence-family-with-descent-data-pushout P s
        ( f (horizontal-map-cocone _ _ c (left-map-span-diagram 𝒮 s))))) ∙
    ( ap
      ( right-map-family-with-descent-data-pushout P
        ( right-map-span-diagram 𝒮 s))
      ( apd f (coherence-square-cocone _ _ c s)))

  section-descent-data-dependent-cocone-span-diagram :
    dependent-cocone-span-diagram c
      ( family-cocone-family-with-descent-data-pushout P) →
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
  pr1 (section-descent-data-dependent-cocone-span-diagram d) a =
    left-map-family-with-descent-data-pushout P a
      ( horizontal-map-dependent-cocone _ _ _ _ d a)
  pr1 (pr2 (section-descent-data-dependent-cocone-span-diagram d)) b =
    right-map-family-with-descent-data-pushout P b
      ( vertical-map-dependent-cocone _ _ _ _ d b)
  pr2 (pr2 (section-descent-data-dependent-cocone-span-diagram d)) s =
    ( inv (coherence-family-with-descent-data-pushout P s _)) ∙
    ( ap
      ( right-map-family-with-descent-data-pushout P
        ( right-map-span-diagram 𝒮 s))
      ( coherence-square-dependent-cocone _ _ _ _ d s))

  abstract
    is-equiv-section-descent-data-dependent-cocone-span-diagram :
      is-equiv section-descent-data-dependent-cocone-span-diagram
    is-equiv-section-descent-data-dependent-cocone-span-diagram =
      is-equiv-map-Σ _
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( is-equiv-left-map-family-with-descent-data-pushout P))
        ( λ tA →
          is-equiv-map-Σ _
            ( is-equiv-map-Π-is-fiberwise-equiv
              ( is-equiv-right-map-family-with-descent-data-pushout P))
            ( λ tB →
              is-equiv-map-Π-is-fiberwise-equiv
                ( λ s →
                  is-equiv-comp _ _
                    ( is-emb-equiv
                      ( right-equiv-family-with-descent-data-pushout P
                        ( right-map-span-diagram 𝒮 s))
                      ( _)
                      ( _))
                    ( is-equiv-inv-concat _ _))))

  triangle-section-descent-data-section-family-cocone-span-diagram :
    coherence-triangle-maps
      ( section-descent-data-section-family-cocone-span-diagram)
      ( section-descent-data-dependent-cocone-span-diagram)
      ( dependent-cocone-map-span-diagram c
        ( family-cocone-family-with-descent-data-pushout P))
  triangle-section-descent-data-section-family-cocone-span-diagram = refl-htpy

  abstract
    is-equiv-section-descent-data-section-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv (section-descent-data-section-family-cocone-span-diagram)
    is-equiv-section-descent-data-section-family-cocone-span-diagram up-c =
      is-equiv-left-map-triangle
        ( section-descent-data-section-family-cocone-span-diagram)
        ( section-descent-data-dependent-cocone-span-diagram)
        ( dependent-cocone-map-span-diagram c
          ( family-cocone-family-with-descent-data-pushout P))
        ( triangle-section-descent-data-section-family-cocone-span-diagram)
        ( dependent-universal-property-universal-property-pushout _ _ _ up-c
          ( family-cocone-family-with-descent-data-pushout P))
        ( is-equiv-section-descent-data-dependent-cocone-span-diagram)
```

As a corollary, for any given section `(tA, tB, tS)` of `(PA, PB, PS)`, there is
a unique section `t : (x : X) → P x` of `P` such that its induced section of
`(PA, PB, PS)` is homotopic to `(tA, tB, tS)`.

**Proof:** Since the map taking sections of `P` to sections of `(PA, PB, PS)` is
an equivalence, it has contractible fibers. The fiber at `(tA, tB, tS)` is the
type of sections of `P` that induce a section of `(PA, PB, PS)` which is
identified with `(tA, tB, tS)`, and such identifications are characterized by
homotopies of sections of `(PA, PB, PS)`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : family-with-descent-data-pushout c l5 l6 l7)
  (t :
    section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P))
  where

  abstract
    uniqueness-section-family-section-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) → family-cocone-family-with-descent-data-pushout P x)
            ( λ h →
              htpy-section-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( section-descent-data-section-family-cocone-span-diagram P h)
                ( t)))
    uniqueness-section-family-section-descent-data-pushout =
      is-contr-equiv'
        ( fiber (section-descent-data-section-family-cocone-span-diagram P) t)
        ( equiv-tot
          ( λ h →
            extensionality-section-descent-data-pushout
              ( descent-data-family-with-descent-data-pushout P)
              ( _)
              ( t)))
        ( is-contr-map-is-equiv
          ( is-equiv-section-descent-data-section-family-cocone-span-diagram P
            ( up-c))
          ( t))

  section-family-section-descent-data-pushout :
    (x : X) → family-cocone-family-with-descent-data-pushout P x
  section-family-section-descent-data-pushout =
    pr1 (center uniqueness-section-family-section-descent-data-pushout)

  htpy-section-family-section-descent-data-pushout :
    htpy-section-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( section-descent-data-section-family-cocone-span-diagram P
        ( section-family-section-descent-data-pushout))
      ( t)
  htpy-section-family-section-descent-data-pushout =
    pr2 (center uniqueness-section-family-section-descent-data-pushout)
```
