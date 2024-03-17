# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-hexagons-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-span-diagrams
open import foundation.equivalences-spans
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.operations-spans
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.action-dependent-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-property-families-of-types-pushouts
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-span-diagrams
open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-equipped-with-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-families-of-types-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The {{#concept "flattening lemma" Disambiguation="pushouts"}} for
[pushouts](synthetic-homotopy-theory.pushouts.md) states that pushouts commute
with [dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
        g
    S -----> B
    |        |
  f |        | j
    V      ⌜ V
    A -----> X
        i
```

with [homotopy](foundation-core.homotopies.md) `H : i ∘ f ~ j ∘ g`, and for any
type family `P` over `X`, the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square. The [span diagram](foundation.span-diagrams.md) in
this square is the
[flattening](synthetic-homotopy-theory.flattening-families-of-types-pushouts.md)
of the type family `P` over `X`.

## Theorems

### The flattening lemma for pushouts

The proof uses the theorem that maps from `Σ`-types are equivalent to dependent
maps over the index type, for which we can invoke the dependent universal
property of the indexing pushout.

```text
module _
  { l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X) (P : X → UU l5)
  where

  cocone-map-flattening-type-family-pushout :
    {l : Level} (Y : UU l) →
    (Σ X P → Y) →
    cocone-span-diagram (span-diagram-flattening-type-family-pushout 𝒮 c P) Y
  cocone-map-flattening-type-family-pushout Y =
    cocone-map-span-diagram
      ( span-diagram-flattening-type-family-pushout 𝒮 c P)
      ( cocone-flattening-type-family-pushout 𝒮 c P)

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    cocone-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)
      ( Y) ≃
    dependent-cocone-span-diagram 𝒮 c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( equiv-htpy-dependent-function-dependent-identification-function-type
                ( Y)
                ( coherence-square-cocone-span-diagram 𝒮 c)
                ( k ∘ left-map-span-diagram 𝒮)
                ( l ∘ right-map-span-diagram 𝒮))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map-span-diagram 𝒮 c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘
        cocone-map-flattening-type-family-pushout Y ∘
        ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( inv-htpy
            ( compute-equiv-htpy-dependent-function-dependent-identification-function-type
              ( Y)
              ( coherence-square-cocone-span-diagram 𝒮 c)
              ( h)))))

  abstract
    flattening-lemma-pushout :
      universal-property-pushout 𝒮 c →
      universal-property-pushout
        ( span-diagram-flattening-type-family-pushout 𝒮 c P)
        ( cocone-flattening-type-family-pushout 𝒮 c P)
    flattening-lemma-pushout U Y =
      is-equiv-left-factor
        ( cocone-map-flattening-type-family-pushout Y)
        ( ind-Σ)
        ( is-equiv-right-factor
          ( map-equiv equiv-ev-pair³)
          ( cocone-map-flattening-type-family-pushout Y ∘ ind-Σ)
          ( is-equiv-map-equiv equiv-ev-pair³)
          ( is-equiv-top-map-triangle
            ( dependent-cocone-map-span-diagram 𝒮 c (λ x → P x → Y))
            ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
            ( map-equiv equiv-ev-pair³ ∘
              cocone-map-flattening-type-family-pushout Y ∘
              ind-Σ)
            ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
            ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
            ( dependent-universal-property-universal-property-pushout 𝒮 c U
              ( λ x → P x → Y))))
        ( is-equiv-ind-Σ)
```

### The flattening lemma with descent data

The proof is carried out by constructing a commuting cube, which has
equivalences for vertical maps, the `cocone-flattening-type-family-pushout`
square for the bottom, and the `cocone-flattening-structure-type-family-pushout`
square for the top.

The bottom is a pushout by the above flattening lemma, which implies that the
top is also a pushout.

The other parts of the cube are defined naturally, and come from the following
map of span diagrams:

```text
  Σ (a : A) (PA a) <------- Σ (s : S) (PA (f s)) -----> Σ (b : B) (PB b)
         |                           |                         |
         |                           |                         |
         v                           v                         v
Σ (a : A) (P (i a)) <---- Σ (s : S) (P (i (f s))) ---> Σ (b : B) (P (j b))
```

where the vertical maps are equivalences given fiberwise by the equivalence of
descent data.

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X)
  ( Y : family-with-descent-data-pushout l5 l6 𝒮 c)
  where

  abstract
    flattening-lemma-descent-data-pushout :
      universal-property-pushout 𝒮 c →
      universal-property-pushout
        ( span-diagram-flattening-family-with-descent-data-pushout 𝒮 c Y)
        ( cocone-flattening-structure-type-family-pushout 𝒮 c Y)
    flattening-lemma-descent-data-pushout H = {!!}

{-
      universal-property-pushout-equiv-cocone-equiv-span-diagram
        ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
        ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
        ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
        ( cocone-flattening-type-family-pushout 𝒮 c Q)
        ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
        ( equiv-cocone-flattening-lemma-descent-data-pushout)
        ( flattening-lemma-pushout 𝒮 c Q H) -}
```

```text
  equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    domain-flattening-structure-type-family-pushout 𝒮 P ≃
    domain-flattening-type-family-pushout 𝒮 c Q
  equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( left-equiv-equiv-structure-type-family-pushout 𝒮 P
        ( descent-data-type-family-pushout 𝒮 c Q)
        ( e))

  map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    domain-flattening-structure-type-family-pushout 𝒮 P →
    domain-flattening-type-family-pushout 𝒮 c Q
  map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout

  equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    codomain-flattening-structure-type-family-pushout 𝒮 P ≃
    codomain-flattening-type-family-pushout 𝒮 c Q
  equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( right-equiv-equiv-structure-type-family-pushout 𝒮 P
        ( descent-data-type-family-pushout 𝒮 c Q)
        ( e))

  map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    codomain-flattening-structure-type-family-pushout 𝒮 P →
    codomain-flattening-type-family-pushout 𝒮 c Q
  map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout

  spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    spanning-type-flattening-structure-type-family-pushout 𝒮 P ≃
    spanning-type-flattening-type-family-pushout 𝒮 c Q
  spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( λ x →
        left-equiv-equiv-structure-type-family-pushout 𝒮 P
          ( descent-data-type-family-pushout 𝒮 c Q)
          ( e)
          ( left-map-span-diagram 𝒮 x))

  spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    spanning-type-flattening-structure-type-family-pushout 𝒮 P →
    spanning-type-flattening-type-family-pushout 𝒮 c Q
  spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      ( spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout)

  left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    coherence-square-maps
      ( spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( left-map-flattening-structure-type-family-pushout 𝒮 P)
      ( left-map-flattening-type-family-pushout 𝒮 c Q)
      ( map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
  left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    refl-htpy

  right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    coherence-square-maps
      ( spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( right-map-flattening-structure-type-family-pushout 𝒮 P)
      ( right-map-flattening-type-family-pushout 𝒮 c Q)
      ( map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
  right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout
    (x , t) =
    eq-pair-Σ
      ( refl)
      ( coherence-equiv-structure-type-family-pushout 𝒮 P
        ( descent-data-type-family-pushout 𝒮 c Q)
        ( e)
        ( x)
        ( t))

  equiv-span-flattening-lemma-descent-data-pushout :
    equiv-span
      ( extend-span
        ( span-flattening-structure-type-family-pushout 𝒮 P)
        ( map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
        ( map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout))
      ( span-flattening-type-family-pushout 𝒮 c Q)
  pr1 equiv-span-flattening-lemma-descent-data-pushout =
    spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr1 (pr2 equiv-span-flattening-lemma-descent-data-pushout) =
    left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr2 (pr2 equiv-span-flattening-lemma-descent-data-pushout) =
    right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout

  equiv-span-diagram-flattening-lemma-descent-data-pushout :
    equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
  pr1 equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr1 (pr2 equiv-span-diagram-flattening-lemma-descent-data-pushout) =
    equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr2 (pr2 equiv-span-diagram-flattening-lemma-descent-data-pushout) =
    equiv-span-flattening-lemma-descent-data-pushout

  left-square-equiv-cocone-flattening-lemma-descent-data-pushout :
    left-coherence-square-equiv-cocone-equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
      ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
      ( cocone-flattening-type-family-pushout 𝒮 c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
  left-square-equiv-cocone-flattening-lemma-descent-data-pushout =
    refl-htpy

  right-square-equiv-cocone-flattening-lemma-descent-data-pushout :
    right-coherence-square-equiv-cocone-equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
      ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
      ( cocone-flattening-type-family-pushout 𝒮 c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
  right-square-equiv-cocone-flattening-lemma-descent-data-pushout =
    refl-htpy

  cube-equiv-cocone-flattening-lemma-descent-data-pushout :
    coherence-cube-equiv-cocone-equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
      ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
      ( cocone-flattening-type-family-pushout 𝒮 c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
      ( left-square-equiv-cocone-flattening-lemma-descent-data-pushout)
      ( right-square-equiv-cocone-flattening-lemma-descent-data-pushout)
  cube-equiv-cocone-flattening-lemma-descent-data-pushout (x , t) =
    ( ap-id _) ∙
    ( triangle-eq-pair-Σ Q
      ( coherence-square-cocone-span-diagram 𝒮 c x)
      ( inv
        ( coherence-equiv-structure-type-family-pushout 𝒮 P
          ( descent-data-type-family-pushout 𝒮 c Q)
          ( e)
          ( x)
          ( t)))) ∙
    ( ap
      ( concat (eq-pair-Σ (coherence-square-cocone-span-diagram 𝒮 c x) refl) _)
      ( ( ( inv
            ( compute-ap-map-Σ-map-base-eq-pair-Σ
              ( right-map-cocone-span-diagram 𝒮 c)
              ( Q)
              ( refl)
              ( inv
                ( coherence-equiv-structure-type-family-pushout 𝒮 P
                  ( descent-data-type-family-pushout 𝒮 c Q)
                  ( e)
                  ( x)
                  ( t))))) ∙
          ( ap
            ( ap (map-Σ-map-base _ Q))
            ( inv
              ( distributive-inv-eq-pair-Σ-refl
                ( coherence-equiv-structure-type-family-pushout 𝒮 P
                  ( descent-data-type-family-pushout 𝒮 c Q)
                  ( e)
                  ( x)
                  ( t)))))) ∙
        ( inv right-unit)))

  equiv-cocone-flattening-lemma-descent-data-pushout :
    equiv-cocone-equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
      ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
      ( cocone-flattening-type-family-pushout 𝒮 c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
  pr1 equiv-cocone-flattening-lemma-descent-data-pushout = id-equiv
  pr1 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout) =
    left-square-equiv-cocone-flattening-lemma-descent-data-pushout
  pr1 (pr2 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout)) =
    right-square-equiv-cocone-flattening-lemma-descent-data-pushout
  pr2 (pr2 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout)) =
    cube-equiv-cocone-flattening-lemma-descent-data-pushout

  abstract
    flattening-lemma-descent-data-pushout :
      universal-property-pushout 𝒮 c →
      universal-property-pushout
        ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
        ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
    flattening-lemma-descent-data-pushout H =
      universal-property-pushout-equiv-cocone-equiv-span-diagram
        ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
        ( cocone-flattening-structure-type-family-pushout 𝒮 c P Q e)
        ( span-diagram-flattening-type-family-pushout 𝒮 c Q)
        ( cocone-flattening-type-family-pushout 𝒮 c Q)
        ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
        ( equiv-cocone-flattening-lemma-descent-data-pushout)
        ( flattening-lemma-pushout 𝒮 c Q H)
```
