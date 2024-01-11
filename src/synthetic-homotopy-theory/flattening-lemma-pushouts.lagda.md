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
open import foundation.extensions-spans
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-span-diagrams
open import synthetic-homotopy-theory.families-of-types-pushouts
open import synthetic-homotopy-theory.flattening-families-of-types-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The {{#concept "flattening lemma" Disambiguation="pushouts"}} for [pushouts](synthetic-homotopy-theory.pushouts.md)
states that pushouts commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
      g
  S -----> B
  |        |
 f|        |j
  V      ⌜ V
  A -----> X
      i
```

with [homotopy](foundation-core.homotopies.md) `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  where

  spanning-type-flattening-pushout : UU (l3 ⊔ l5)
  spanning-type-flattening-pushout =
    Σ ( spanning-type-span-diagram s)
      ( P ∘ left-map-cocone-span-diagram s c ∘ left-map-span-diagram s)

  domain-flattening-pushout : UU (l1 ⊔ l5)
  domain-flattening-pushout =
    Σ ( domain-span-diagram s) (P ∘ left-map-cocone-span-diagram s c)

  codomain-flattening-pushout : UU (l2 ⊔ l5)
  codomain-flattening-pushout =
    Σ ( codomain-span-diagram s) (P ∘ right-map-cocone-span-diagram s c)

  left-map-flattening-pushout :
    spanning-type-flattening-pushout → domain-flattening-pushout
  left-map-flattening-pushout =
    map-Σ-map-base
      ( left-map-span-diagram s)
      ( P ∘ left-map-cocone-span-diagram s c)

  right-map-flattening-pushout :
    spanning-type-flattening-pushout → codomain-flattening-pushout
  right-map-flattening-pushout =
    map-Σ
      ( P ∘ right-map-cocone-span-diagram s c)
      ( right-map-span-diagram s)
      ( λ x → tr P (coherence-square-cocone-span-diagram s c x))

  span-diagram-flattening-pushout : span-diagram (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-diagram-flattening-pushout =
    make-span-diagram
      ( left-map-flattening-pushout)
      ( right-map-flattening-pushout)

  left-map-cocone-flattening-pushout :
    domain-flattening-pushout → Σ X P
  left-map-cocone-flattening-pushout =
    map-Σ-map-base (left-map-cocone-span-diagram s c) P

  right-map-cocone-flattening-pushout :
    codomain-flattening-pushout → Σ X P
  right-map-cocone-flattening-pushout =
    map-Σ-map-base (right-map-cocone-span-diagram s c) P

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( right-map-flattening-pushout)
      ( left-map-flattening-pushout)
      ( right-map-cocone-flattening-pushout)
      ( left-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout =
    coherence-square-maps-map-Σ-map-base P
      ( right-map-span-diagram s)
      ( left-map-span-diagram s)
      ( right-map-cocone-span-diagram s c)
      ( left-map-cocone-span-diagram s c)
      ( coherence-square-cocone-span-diagram s c)

  cocone-flattening-pushout :
    cocone-span-diagram span-diagram-flattening-pushout (Σ X P)
  pr1 cocone-flattening-pushout =
    left-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout) =
    right-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout) =
    coherence-square-cocone-flattening-pushout

  statement-flattening-lemma-pushout : UUω
  statement-flattening-lemma-pushout =
    dependent-universal-property-pushout s c →
    universal-property-pushout
      ( span-diagram-flattening-pushout)
      ( cocone-flattening-pushout)
```

### The statement of the flattening lemma for pushouts, phrased using descent data

The above statement of the flattening lemma works with a provided type family
over the pushout. We can instead accept a definition of this family via descent
data for the pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X)
  ( P : structure-type-family-pushout l5 s)
  ( Q : X → UU l5)
  ( e :
    equiv-structure-type-family-pushout s P
      ( descent-data-type-family-pushout s c Q))
  where

  statement-flattening-lemma-structure-type-family-pushout : UUω
  statement-flattening-lemma-structure-type-family-pushout =
    dependent-universal-property-pushout s c →
    universal-property-pushout
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
```

## Properties

### Proof of the flattening lemma for pushouts

The proof uses the theorem that maps from `Σ`-types are equivalent to dependent
maps over the index type, for which we can invoke the dependent universal
property of the indexing pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  where

  cocone-map-flattening-pushout :
    {l : Level} (Y : UU l) →
    (Σ X P → Y) → cocone-span-diagram (span-diagram-flattening-pushout s c P) Y
  cocone-map-flattening-pushout Y =
    cocone-map-span-diagram
      ( span-diagram-flattening-pushout s c P)
      ( cocone-flattening-pushout s c P)

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    Σ ( (a : domain-span-diagram s) →
        P (left-map-cocone-span-diagram s c a) → Y)
      ( λ k →
        Σ ( (b : codomain-span-diagram s) →
            P (right-map-cocone-span-diagram s c b) → Y)
          ( λ l →
            ( x : spanning-type-span-diagram s)
            ( t :
              P (left-map-cocone-span-diagram s c
                ( left-map-span-diagram s x))) →
            ( k (left-map-span-diagram s x) t) ＝
            ( l ( right-map-span-diagram s x)
                ( tr P (coherence-square-cocone-span-diagram s c x) t)))) ≃
    dependent-cocone-span-diagram s c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( equiv-htpy-dependent-function-dependent-identification-function-type
                ( Y)
                ( coherence-square-cocone-span-diagram s c)
                ( k ∘ left-map-span-diagram s)
                ( l ∘ right-map-span-diagram s))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map-span-diagram s c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( eq-htpy
          ( inv-htpy
            ( compute-equiv-htpy-dependent-function-dependent-identification-function-type
              ( Y)
              ( coherence-square-cocone-span-diagram s c)
              ( h)))))

  flattening-lemma-pushout :
    statement-flattening-lemma-pushout s c P
  flattening-lemma-pushout dup-pushout Y =
    is-equiv-left-factor
      ( cocone-map-flattening-pushout Y)
      ( ind-Σ)
      ( is-equiv-right-factor
        ( map-equiv equiv-ev-pair³)
        ( cocone-map-flattening-pushout Y ∘ ind-Σ)
        ( is-equiv-map-equiv equiv-ev-pair³)
        ( is-equiv-top-map-triangle
          ( dependent-cocone-map-span-diagram s c (λ x → P x → Y))
          ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
          ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
          ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( dup-pushout (λ x → P x → Y))))
      ( is-equiv-ind-Σ)
```

### Proof of the descent data statement of the flattening lemma

The proof is carried out by constructing a commuting cube, which has
equivalences for vertical maps, the `cocone-flattening-pushout` square for the
bottom, and the `cocone-flattening-structure-type-family-pushout` square for the top.

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
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X)
  ( P : structure-type-family-pushout l5 s)
  ( Q : X → UU l5)
  ( e :
    equiv-structure-type-family-pushout s P
      ( descent-data-type-family-pushout s c Q))
  where

  equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    domain-flattening-structure-type-family-pushout s P ≃
    domain-flattening-pushout s c Q
  equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( left-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    domain-flattening-structure-type-family-pushout s P →
    domain-flattening-pushout s c Q
  map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout

  equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    codomain-flattening-structure-type-family-pushout s P ≃
    codomain-flattening-pushout s c Q
  equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( right-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    codomain-flattening-structure-type-family-pushout s P →
    codomain-flattening-pushout s c Q
  map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout

  spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    spanning-type-flattening-structure-type-family-pushout s P ≃
    spanning-type-flattening-pushout s c Q
  spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-tot
      ( λ x →
        left-equiv-equiv-structure-type-family-pushout s P
          ( descent-data-type-family-pushout s c Q)
          ( e)
          ( left-map-span-diagram s x))

  spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    spanning-type-flattening-structure-type-family-pushout s P →
    spanning-type-flattening-pushout s c Q
  spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    map-equiv
      ( spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout)

  left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    coherence-square-maps
      ( spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( left-map-flattening-structure-type-family-pushout s P)
      ( left-map-flattening-pushout s c Q)
      ( map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
  left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout =
    refl-htpy

  right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout :
    coherence-square-maps
      ( spanning-map-equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( right-map-flattening-structure-type-family-pushout s P)
      ( right-map-flattening-pushout s c Q)
      ( map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
  right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout
    (x , t) =
    eq-pair-Σ
      ( refl)
      ( coherence-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e)
        ( x)
        ( t))

  equiv-span-flattening-lemma-descent-data-pushout :
    equiv-span
      ( extend-span
        ( span-span-diagram (flattening-structure-type-family-pushout s P))
        ( map-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout)
        ( map-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout))
      ( span-span-diagram (span-diagram-flattening-pushout s c Q))
  pr1 equiv-span-flattening-lemma-descent-data-pushout =
    spanning-equiv-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr1 (pr2 equiv-span-flattening-lemma-descent-data-pushout) =
    left-square-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr2 (pr2 equiv-span-flattening-lemma-descent-data-pushout) =
    right-square-equiv-span-diagram-flattening-lemma-descent-data-pushout

  equiv-span-diagram-flattening-lemma-descent-data-pushout :
    equiv-span-diagram
     ( flattening-structure-type-family-pushout s P)
     ( span-diagram-flattening-pushout s c Q)
  pr1 equiv-span-diagram-flattening-lemma-descent-data-pushout =
    equiv-domain-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr1 (pr2 equiv-span-diagram-flattening-lemma-descent-data-pushout) =
    equiv-codomain-equiv-span-diagram-flattening-lemma-descent-data-pushout
  pr2 (pr2 equiv-span-diagram-flattening-lemma-descent-data-pushout) =
    equiv-span-flattening-lemma-descent-data-pushout

  left-square-equiv-cocone-flattening-lemma-descent-data-pushout :
    left-coherence-square-equiv-cocone-equiv-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
      ( span-diagram-flattening-pushout s c Q)
      ( cocone-flattening-pushout s c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
  left-square-equiv-cocone-flattening-lemma-descent-data-pushout =
    refl-htpy

  right-square-equiv-cocone-flattening-lemma-descent-data-pushout :
    right-coherence-square-equiv-cocone-equiv-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
      ( span-diagram-flattening-pushout s c Q)
      ( cocone-flattening-pushout s c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
  right-square-equiv-cocone-flattening-lemma-descent-data-pushout =
    refl-htpy

  cube-equiv-cocone-flattening-lemma-descent-data-pushout :
    coherence-cube-equiv-cocone-equiv-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
      ( span-diagram-flattening-pushout s c Q)
      ( cocone-flattening-pushout s c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( id-equiv)
      ( left-square-equiv-cocone-flattening-lemma-descent-data-pushout)
      ( right-square-equiv-cocone-flattening-lemma-descent-data-pushout)
  cube-equiv-cocone-flattening-lemma-descent-data-pushout (x , t) =
    ( ap-id _) ∙
    ( triangle-eq-pair-Σ Q
      ( coherence-square-cocone-span-diagram s c x)
      ( inv
        ( coherence-equiv-structure-type-family-pushout s P
          ( descent-data-type-family-pushout s c Q)
          ( e)
          ( x)
          ( t)))) ∙
    ( ap
      ( concat (eq-pair-Σ (coherence-square-cocone-span-diagram s c x) refl) _)
      ( ( ( inv
            ( compute-ap-map-Σ-map-base-eq-pair-Σ
              ( right-map-cocone-span-diagram s c)
              ( Q)
              ( refl)
              ( inv
                ( coherence-equiv-structure-type-family-pushout s P
                  ( descent-data-type-family-pushout s c Q)
                  ( e)
                  ( x)
                  ( t))))) ∙
          ( ap
            ( ap (map-Σ-map-base _ Q))
            ( inv
              ( distributive-inv-eq-pair-Σ-refl
                ( coherence-equiv-structure-type-family-pushout s P
                  ( descent-data-type-family-pushout s c Q)
                  ( e)
                  ( x)
                  ( t)))))) ∙
        ( inv right-unit)))

  equiv-cocone-flattening-lemma-descent-data-pushout :
    equiv-cocone-equiv-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
      ( span-diagram-flattening-pushout s c Q)
      ( cocone-flattening-pushout s c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
  pr1 equiv-cocone-flattening-lemma-descent-data-pushout = id-equiv
  pr1 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout) =
    left-square-equiv-cocone-flattening-lemma-descent-data-pushout
  pr1 (pr2 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout)) =
    right-square-equiv-cocone-flattening-lemma-descent-data-pushout
  pr2 (pr2 (pr2 equiv-cocone-flattening-lemma-descent-data-pushout)) =
    cube-equiv-cocone-flattening-lemma-descent-data-pushout

  flattening-lemma-descent-data-pushout :
    statement-flattening-lemma-structure-type-family-pushout s c P Q e
  flattening-lemma-descent-data-pushout H =
    universal-property-pushout-equiv-cocone-equiv-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( cocone-flattening-structure-type-family-pushout s c P Q e)
      ( span-diagram-flattening-pushout s c Q)
      ( cocone-flattening-pushout s c Q)
      ( equiv-span-diagram-flattening-lemma-descent-data-pushout)
      ( equiv-cocone-flattening-lemma-descent-data-pushout)
      ( flattening-lemma-pushout s c Q H)
```
