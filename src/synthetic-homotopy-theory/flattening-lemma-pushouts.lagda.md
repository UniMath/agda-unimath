# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
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

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equifibered-span-diagrams
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-equifibered-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "flattening lemma" Disambiguation="for pushouts" Agda=flattening-lemma-pushout Agda=flattening-lemma-descent-data-pushout}}
for [pushouts](synthetic-homotopy-theory.pushouts.md) states that pushouts
commute with [dependent pair types](foundation.dependent-pair-types.md). More
precisely, given a pushout square

```text
         g
    S ------> B
    |         |
  f |         | j
    ∨       ⌜ ∨
    A ------> X
         i
```

with homotopy `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
commuting square

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           ∨                                               ⌜ ∨
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  where

  vertical-map-span-flattening-pushout :
    Σ S (P ∘ horizontal-map-cocone f g c ∘ f) →
    Σ A (P ∘ horizontal-map-cocone f g c)
  vertical-map-span-flattening-pushout =
    map-Σ-map-base f (P ∘ horizontal-map-cocone f g c)

  horizontal-map-span-flattening-pushout :
    Σ S (P ∘ horizontal-map-cocone f g c ∘ f) →
    Σ B (P ∘ vertical-map-cocone f g c)
  horizontal-map-span-flattening-pushout =
    map-Σ
      ( P ∘ vertical-map-cocone f g c)
      ( g)
      ( λ s → tr P (coherence-square-cocone f g c s))

  horizontal-map-cocone-flattening-pushout :
    Σ A (P ∘ horizontal-map-cocone f g c) → Σ X P
  horizontal-map-cocone-flattening-pushout =
    map-Σ-map-base (horizontal-map-cocone f g c) P

  vertical-map-cocone-flattening-pushout :
    Σ B (P ∘ vertical-map-cocone f g c) → Σ X P
  vertical-map-cocone-flattening-pushout =
    map-Σ-map-base (vertical-map-cocone f g c) P

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( horizontal-map-span-flattening-pushout)
      ( vertical-map-span-flattening-pushout)
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout =
    coherence-square-maps-map-Σ-map-base P g f
      ( vertical-map-cocone f g c)
      ( horizontal-map-cocone f g c)
      ( coherence-square-cocone f g c)

  cocone-flattening-pushout :
    cocone
      ( vertical-map-span-flattening-pushout)
      ( horizontal-map-span-flattening-pushout)
      ( Σ X P)
  pr1 cocone-flattening-pushout =
    horizontal-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout) =
    vertical-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout) =
    coherence-square-cocone-flattening-pushout

  flattening-lemma-pushout-statement : UUω
  flattening-lemma-pushout-statement =
    universal-property-pushout f g c →
    universal-property-pushout
      ( vertical-map-span-flattening-pushout)
      ( horizontal-map-span-flattening-pushout)
      ( cocone-flattening-pushout)

module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (P : X → UU l5)
  where

  span-diagram-flattening-pushout : span-diagram (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-diagram-flattening-pushout =
    make-span-diagram
      ( vertical-map-span-flattening-pushout P _ _ c)
      ( horizontal-map-span-flattening-pushout P _ _ c)
```

### The statement of the flattening lemma for pushouts, using descent data

The above statement of the flattening lemma works with a provided type family
over the pushout. We can instead accept a definition of this family via descent
data for the pushout.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  vertical-map-span-flattening-descent-data-pushout :
    Σ ( spanning-type-span-diagram 𝒮)
      ( left-family-descent-data-pushout P ∘ left-map-span-diagram 𝒮) →
    Σ ( domain-span-diagram 𝒮) (left-family-descent-data-pushout P)
  vertical-map-span-flattening-descent-data-pushout =
    map-Σ-map-base
      ( left-map-span-diagram 𝒮)
      ( left-family-descent-data-pushout P)

  horizontal-map-span-flattening-descent-data-pushout :
    Σ ( spanning-type-span-diagram 𝒮)
      ( left-family-descent-data-pushout P ∘ left-map-span-diagram 𝒮) →
    Σ ( codomain-span-diagram 𝒮) (right-family-descent-data-pushout P)
  horizontal-map-span-flattening-descent-data-pushout =
    map-Σ
      ( right-family-descent-data-pushout P)
      ( right-map-span-diagram 𝒮)
      ( map-family-descent-data-pushout P)

  span-diagram-flattening-descent-data-pushout :
    span-diagram (l1 ⊔ l4) (l2 ⊔ l5) (l3 ⊔ l4)
  span-diagram-flattening-descent-data-pushout =
    make-span-diagram
      ( vertical-map-span-flattening-descent-data-pushout)
      ( horizontal-map-span-flattening-descent-data-pushout)

module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : descent-data-pushout (make-span-diagram f g) l5 l6)
  ( Q : X → UU l7)
  ( e :
    equiv-descent-data-pushout P (descent-data-family-cocone-span-diagram c Q))
  where

  horizontal-map-cocone-flattening-descent-data-pushout :
    Σ A (left-family-descent-data-pushout P) → Σ X Q
  horizontal-map-cocone-flattening-descent-data-pushout =
    map-Σ Q
      ( horizontal-map-cocone f g c)
      ( left-map-equiv-descent-data-pushout
        ( P)
        ( descent-data-family-cocone-span-diagram c Q)
        ( e))

  vertical-map-cocone-flattening-descent-data-pushout :
    Σ B (right-family-descent-data-pushout P) → Σ X Q
  vertical-map-cocone-flattening-descent-data-pushout =
    map-Σ Q
      ( vertical-map-cocone f g c)
      ( right-map-equiv-descent-data-pushout
        ( P)
        ( descent-data-family-cocone-span-diagram c Q)
        ( e))

  coherence-square-cocone-flattening-descent-data-pushout :
    coherence-square-maps
      ( horizontal-map-span-flattening-descent-data-pushout P)
      ( vertical-map-span-flattening-descent-data-pushout P)
      ( vertical-map-cocone-flattening-descent-data-pushout)
      ( horizontal-map-cocone-flattening-descent-data-pushout)
  coherence-square-cocone-flattening-descent-data-pushout =
    htpy-map-Σ Q
      ( coherence-square-cocone f g c)
      ( ( left-map-equiv-descent-data-pushout
          ( P)
          ( descent-data-family-cocone-span-diagram c Q)
          ( e)) ∘
        ( f))
      ( inv-htpy ∘
        coherence-equiv-descent-data-pushout
          ( P)
          ( descent-data-family-cocone-span-diagram c Q)
          ( e))

  cocone-flattening-descent-data-pushout :
    cocone
      ( vertical-map-span-flattening-descent-data-pushout P)
      ( horizontal-map-span-flattening-descent-data-pushout P)
      ( Σ X Q)
  pr1 cocone-flattening-descent-data-pushout =
    horizontal-map-cocone-flattening-descent-data-pushout
  pr1 (pr2 cocone-flattening-descent-data-pushout) =
    vertical-map-cocone-flattening-descent-data-pushout
  pr2 (pr2 cocone-flattening-descent-data-pushout) =
    coherence-square-cocone-flattening-descent-data-pushout

  flattening-lemma-descent-data-pushout-statement : UUω
  flattening-lemma-descent-data-pushout-statement =
    universal-property-pushout f g c →
    universal-property-pushout
      ( vertical-map-span-flattening-descent-data-pushout P)
      ( horizontal-map-span-flattening-descent-data-pushout P)
      ( cocone-flattening-descent-data-pushout)
```

### The statement of the flattening lemma for pushouts, using equifibered diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : equifibered-span-diagram 𝒮 l4 l5 l6)
  where

  vertical-map-span-flattening-equifibered-span-diagram :
    Σ ( spanning-type-span-diagram 𝒮)
      ( spanning-type-family-equifibered-span-diagram P) →
    Σ ( domain-span-diagram 𝒮)
      ( left-family-equifibered-span-diagram P)
  vertical-map-span-flattening-equifibered-span-diagram =
    map-Σ
      ( left-family-equifibered-span-diagram P)
      ( left-map-span-diagram 𝒮)
      ( map-left-family-equifibered-span-diagram P)

  horizontal-map-span-flattening-equifibered-span-diagram :
    Σ ( spanning-type-span-diagram 𝒮)
      ( spanning-type-family-equifibered-span-diagram P) →
    Σ ( codomain-span-diagram 𝒮)
      ( right-family-equifibered-span-diagram P)
  horizontal-map-span-flattening-equifibered-span-diagram =
    map-Σ
      ( right-family-equifibered-span-diagram P)
      ( right-map-span-diagram 𝒮)
      ( map-right-family-equifibered-span-diagram P)

  span-diagram-flattening-equifibered-span-diagram :
    span-diagram (l1 ⊔ l4) (l2 ⊔ l5) (l3 ⊔ l6)
  span-diagram-flattening-equifibered-span-diagram =
    make-span-diagram
      ( vertical-map-span-flattening-equifibered-span-diagram)
      ( horizontal-map-span-flattening-equifibered-span-diagram)

module _
  { l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : equifibered-span-diagram (make-span-diagram f g) l5 l6 l7)
  ( Q : X → UU l8)
  ( e :
    equiv-equifibered-span-diagram
      ( P)
      ( equifibered-span-diagram-family-cocone-span-diagram c Q))
  where

  horizontal-map-cocone-flattening-equifibered-span-diagram :
    Σ A (left-family-equifibered-span-diagram P) → Σ X Q
  horizontal-map-cocone-flattening-equifibered-span-diagram =
    map-Σ Q
      ( horizontal-map-cocone f g c)
      ( left-map-equiv-equifibered-span-diagram
        ( P)
        ( equifibered-span-diagram-family-cocone-span-diagram c Q)
        ( e))

  vertical-map-cocone-flattening-equifibered-span-diagram :
    Σ B (right-family-equifibered-span-diagram P) → Σ X Q
  vertical-map-cocone-flattening-equifibered-span-diagram =
    map-Σ Q
      ( vertical-map-cocone f g c)
      ( right-map-equiv-equifibered-span-diagram
        ( P)
        ( equifibered-span-diagram-family-cocone-span-diagram c Q)
        ( e))

  map-left-family-flattening-equifibered-span-diagram :
    (s : S) →
    spanning-type-family-equifibered-span-diagram P s →
    Q (horizontal-map-cocone f g c (f s))
  map-left-family-flattening-equifibered-span-diagram s =
    left-map-equiv-equifibered-span-diagram
      ( P)
      ( equifibered-span-diagram-family-cocone-span-diagram c Q)
      ( e)
      ( f s) ∘
    map-left-family-equifibered-span-diagram P s

  coherence-map-flattening-equifibered-span-diagram :
    (s : S) (t : spanning-type-family-equifibered-span-diagram P s) →
    tr Q
      ( coherence-square-cocone f g c s)
      ( map-left-family-flattening-equifibered-span-diagram s t) ＝
    right-map-equiv-equifibered-span-diagram
      ( P)
      ( equifibered-span-diagram-family-cocone-span-diagram c Q)
      ( e)
      ( g s)
      ( map-right-family-equifibered-span-diagram P s t)
  coherence-map-flattening-equifibered-span-diagram s t =
    ap
      ( tr Q (coherence-square-cocone f g c s))
      ( coherence-left-equiv-equifibered-span-diagram
        ( P)
        ( equifibered-span-diagram-family-cocone-span-diagram c Q)
        ( e)
        ( s)
        ( t)) ∙
    inv
      ( coherence-right-equiv-equifibered-span-diagram
        ( P)
        ( equifibered-span-diagram-family-cocone-span-diagram c Q)
        ( e)
        ( s)
        ( t))

  coherence-square-cocone-flattening-equifibered-span-diagram :
    coherence-square-maps
      ( horizontal-map-span-flattening-equifibered-span-diagram P)
      ( vertical-map-span-flattening-equifibered-span-diagram P)
      ( vertical-map-cocone-flattening-equifibered-span-diagram)
      ( horizontal-map-cocone-flattening-equifibered-span-diagram)
  coherence-square-cocone-flattening-equifibered-span-diagram =
    htpy-map-Σ Q
      ( coherence-square-cocone f g c)
      ( map-left-family-flattening-equifibered-span-diagram)
      ( coherence-map-flattening-equifibered-span-diagram)

  cocone-flattening-equifibered-span-diagram :
    cocone
      ( vertical-map-span-flattening-equifibered-span-diagram P)
      ( horizontal-map-span-flattening-equifibered-span-diagram P)
      ( Σ X Q)
  cocone-flattening-equifibered-span-diagram =
    ( horizontal-map-cocone-flattening-equifibered-span-diagram ,
      vertical-map-cocone-flattening-equifibered-span-diagram ,
      coherence-square-cocone-flattening-equifibered-span-diagram)

  flattening-lemma-equifibered-span-diagram-statement : UUω
  flattening-lemma-equifibered-span-diagram-statement =
    universal-property-pushout f g c →
    universal-property-pushout
      ( vertical-map-span-flattening-equifibered-span-diagram P)
      ( horizontal-map-span-flattening-equifibered-span-diagram P)
      ( cocone-flattening-equifibered-span-diagram)
```

## Properties

### Proof of the flattening lemma for pushouts, using descent data

The proof uses the theorem that maps from sigma types are equivalent to
dependent maps over the index type, for which we can invoke the dependent
universal property of the indexing pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  where

  cocone-map-flattening-pushout :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cocone
      ( vertical-map-span-flattening-pushout P f g c)
      ( horizontal-map-span-flattening-pushout P f g c)
      ( Y)
  cocone-map-flattening-pushout Y =
    cocone-map
      ( vertical-map-span-flattening-pushout P f g c)
      ( horizontal-map-span-flattening-pushout P f g c)
      ( cocone-flattening-pushout P f g c)

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    Σ ( (a : A) → P (horizontal-map-cocone f g c a) → Y)
      ( λ k →
        Σ ( (b : B) → P (vertical-map-cocone f g c b) → Y)
          ( λ l →
            ( s : S) (t : P (horizontal-map-cocone f g c (f s))) →
            ( k (f s) t) ＝
            ( l (g s) (tr P (coherence-square-cocone f g c s) t)))) ≃
    dependent-cocone f g c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( equiv-htpy-dependent-function-dependent-identification-function-type
                ( Y)
                ( coherence-square-cocone f g c)
                ( k ∘ f)
                ( l ∘ g))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map f g c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( inv-htpy
            ( compute-equiv-htpy-dependent-function-dependent-identification-function-type
              ( Y)
              ( coherence-square-cocone f g c)
              ( h)))))
  abstract
    flattening-lemma-pushout :
      flattening-lemma-pushout-statement P f g c
    flattening-lemma-pushout up-c Y =
      is-equiv-left-factor
        ( cocone-map-flattening-pushout Y)
        ( ind-Σ)
        ( is-equiv-right-factor
          ( map-equiv equiv-ev-pair³)
          ( cocone-map-flattening-pushout Y ∘ ind-Σ)
          ( is-equiv-map-equiv equiv-ev-pair³)
          ( is-equiv-top-map-triangle
            ( dependent-cocone-map f g c (λ x → P x → Y))
            ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
            ( ( map-equiv equiv-ev-pair³) ∘
              ( cocone-map-flattening-pushout Y) ∘
              ( ind-Σ))
            ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
            ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
            ( dependent-universal-property-universal-property-pushout _ _ _ up-c
              ( λ x → P x → Y))))
        ( is-equiv-ind-Σ)
```

### Proof of the descent data statement of the flattening lemma

The proof is carried out by constructing a commuting cube, which has
equivalences for vertical maps, the `cocone-flattening-pushout` square for the
bottom, and the `cocone-flattening-descent-data-pushout` square for the top.

The bottom is a pushout by the above flattening lemma, which implies that the
top is also a pushout.

The other parts of the cube are defined naturally, and come from the following
map of spans:

```text
  Σ (a : A) (PA a) <------- Σ (s : S) (PA (f s)) -----> Σ (b : B) (PB b)
         |                           |                         |
         |                           |                         |
         ∨                           ∨                         ∨
Σ (a : A) (P (i a)) <---- Σ (s : S) (P (i (f s))) ---> Σ (b : B) (P (j b))
```

where the vertical maps are equivalences given fiberwise by the equivalence of
descent data.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : descent-data-pushout (make-span-diagram f g) l5 l6)
  ( Q : X → UU l7)
  ( e :
    equiv-descent-data-pushout P (descent-data-family-cocone-span-diagram c Q))
  where

  coherence-cube-flattening-lemma-descent-data-pushout :
    coherence-cube-maps
      ( vertical-map-span-flattening-pushout Q f g c)
      ( horizontal-map-span-flattening-pushout Q f g c)
      ( horizontal-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-span-flattening-descent-data-pushout P)
      ( horizontal-map-span-flattening-descent-data-pushout P)
      ( horizontal-map-cocone-flattening-descent-data-pushout f g c P Q e)
      ( vertical-map-cocone-flattening-descent-data-pushout f g c P Q e)
      ( tot
        ( ( left-map-equiv-descent-data-pushout
            ( P)
            ( descent-data-family-cocone-span-diagram c Q)
            ( e)) ∘
          ( f)))
      ( tot
        ( left-map-equiv-descent-data-pushout
          ( P)
          ( descent-data-family-cocone-span-diagram c Q)
          ( e)))
      ( tot
        ( right-map-equiv-descent-data-pushout
          ( P)
          ( descent-data-family-cocone-span-diagram c Q)
          ( e)))
      ( id)
      ( coherence-square-cocone-flattening-descent-data-pushout f g c P Q e)
      ( refl-htpy)
      ( htpy-map-Σ
        ( Q ∘ vertical-map-cocone f g c)
        ( refl-htpy)
        ( λ s →
          ( tr Q (coherence-square-cocone f g c s)) ∘
          ( left-map-equiv-descent-data-pushout
            ( P)
            ( descent-data-family-cocone-span-diagram c Q)
            ( e)
            ( f s)))
        ( inv-htpy ∘
          coherence-equiv-descent-data-pushout
            ( P)
            ( descent-data-family-cocone-span-diagram c Q)
            ( e)))
      ( refl-htpy)
      ( refl-htpy)
      ( coherence-square-cocone-flattening-pushout Q f g c)
  coherence-cube-flattening-lemma-descent-data-pushout (s , t) =
    ( ap-id
      ( coherence-square-cocone-flattening-descent-data-pushout f g c P Q e
        ( s , t))) ∙
    ( triangle-eq-pair-Σ Q
      ( coherence-square-cocone f g c s)
      ( inv
        ( coherence-equiv-descent-data-pushout
          ( P)
          ( descent-data-family-cocone-span-diagram c Q)
          ( e)
          ( s)
          ( t)))) ∙
    ( ap
      ( eq-pair-Σ (coherence-square-cocone f g c s) refl ∙_)
      ( inv
        ( ( right-unit) ∙
          ( compute-ap-map-Σ-map-base-eq-pair-Σ
            ( vertical-map-cocone f g c)
            ( Q)
            ( refl)
            ( inv
              ( coherence-equiv-descent-data-pushout
                ( P)
                ( descent-data-family-cocone-span-diagram c Q)
                ( e)
                ( s)
                ( t)))))))

  abstract
    flattening-lemma-descent-data-pushout :
      flattening-lemma-descent-data-pushout-statement f g c P Q e
    flattening-lemma-descent-data-pushout up-c =
      universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
        ( vertical-map-span-flattening-pushout Q f g c)
        ( horizontal-map-span-flattening-pushout Q f g c)
        ( horizontal-map-cocone-flattening-pushout Q f g c)
        ( vertical-map-cocone-flattening-pushout Q f g c)
        ( vertical-map-span-flattening-descent-data-pushout P)
        ( horizontal-map-span-flattening-descent-data-pushout P)
        ( horizontal-map-cocone-flattening-descent-data-pushout f g c P Q e)
        ( vertical-map-cocone-flattening-descent-data-pushout f g c P Q e)
        ( equiv-tot
          ( ( left-equiv-equiv-descent-data-pushout
              ( P)
              ( descent-data-family-cocone-span-diagram c Q)
              ( e)) ∘
            ( f)))
        ( equiv-tot
          ( left-equiv-equiv-descent-data-pushout
            ( P)
            ( descent-data-family-cocone-span-diagram c Q)
            ( e)))
        ( equiv-tot
          ( right-equiv-equiv-descent-data-pushout
            ( P)
            ( descent-data-family-cocone-span-diagram c Q)
            ( e)))
        ( id-equiv)
        ( coherence-square-cocone-flattening-descent-data-pushout f g c P Q e)
        ( refl-htpy)
        ( htpy-map-Σ
          ( Q ∘ vertical-map-cocone f g c)
          ( refl-htpy)
          ( λ s →
            ( tr Q (coherence-square-cocone f g c s)) ∘
            ( left-map-equiv-descent-data-pushout
              ( P)
              ( descent-data-family-cocone-span-diagram c Q)
              ( e)
              ( f s)))
          ( inv-htpy ∘
            coherence-equiv-descent-data-pushout
              ( P)
              ( descent-data-family-cocone-span-diagram c Q)
              ( e)))
        ( refl-htpy)
        ( refl-htpy)
        ( coherence-square-cocone-flattening-pushout Q f g c)
        ( coherence-cube-flattening-lemma-descent-data-pushout)
        ( flattening-lemma-pushout Q f g c up-c)
```

### Proof of the flattening lemma for pushouts, using equifibered diagrams

The proof is carried out by constructing a commuting cube with the standard
flattening square for `Q` as bottom face and the equifibered flattening square
for `P` as top face. The vertical faces are induced by the equivalence `e`.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : equifibered-span-diagram (make-span-diagram f g) l5 l6 l7)
  ( Q : X → UU l8)
  ( e :
    equiv-equifibered-span-diagram
      ( P)
      ( equifibered-span-diagram-family-cocone-span-diagram c Q))
  where

  equiv-source-cube-flattening-equifibered-span-diagram :
    Σ S (spanning-type-family-equifibered-span-diagram P) ≃
    Σ S (Q ∘ horizontal-map-cocone f g c ∘ f)
  equiv-source-cube-flattening-equifibered-span-diagram =
    equiv-tot
      ( λ x →
        left-equiv-equiv-equifibered-span-diagram
          ( P)
          ( equifibered-span-diagram-family-cocone-span-diagram c Q)
          ( e)
          ( f x) ∘e
        ( equiv-left-family-equifibered-span-diagram P x))

  map-source-cube-flattening-equifibered-span-diagram :
    Σ S (spanning-type-family-equifibered-span-diagram P) →
    Σ S (Q ∘ horizontal-map-cocone f g c ∘ f)
  map-source-cube-flattening-equifibered-span-diagram =
    map-equiv equiv-source-cube-flattening-equifibered-span-diagram

  back-right-coherence-cube-flattening-lemma-equifibered-span-diagram :
    coherence-square-maps
      ( horizontal-map-span-flattening-equifibered-span-diagram P)
      ( map-source-cube-flattening-equifibered-span-diagram)
      ( tot
        ( right-map-equiv-equifibered-span-diagram
          ( P)
          ( equifibered-span-diagram-family-cocone-span-diagram c Q)
          ( e)))
      ( horizontal-map-span-flattening-pushout Q f g c)
  back-right-coherence-cube-flattening-lemma-equifibered-span-diagram =
    htpy-map-Σ
      ( Q ∘ vertical-map-cocone f g c)
      ( refl-htpy)
      ( λ s →
        ( tr Q (coherence-square-cocone f g c s)) ∘
        ( map-left-family-flattening-equifibered-span-diagram f g c P Q e s))
      ( coherence-map-flattening-equifibered-span-diagram f g c P Q e)

  coherence-cube-flattening-lemma-equifibered-span-diagram :
    coherence-cube-maps
      ( vertical-map-span-flattening-pushout Q f g c)
      ( horizontal-map-span-flattening-pushout Q f g c)
      ( horizontal-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-span-flattening-equifibered-span-diagram P)
      ( horizontal-map-span-flattening-equifibered-span-diagram P)
      ( horizontal-map-cocone-flattening-equifibered-span-diagram f g c P Q e)
      ( vertical-map-cocone-flattening-equifibered-span-diagram f g c P Q e)
      ( map-source-cube-flattening-equifibered-span-diagram)
      ( tot
        ( left-map-equiv-equifibered-span-diagram
          ( P)
          ( equifibered-span-diagram-family-cocone-span-diagram c Q)
          ( e)))
      ( tot
        ( right-map-equiv-equifibered-span-diagram
          ( P)
          ( equifibered-span-diagram-family-cocone-span-diagram c Q)
          ( e)))
      ( id)
      ( coherence-square-cocone-flattening-equifibered-span-diagram
        f g c P Q e)
      ( refl-htpy)
      ( back-right-coherence-cube-flattening-lemma-equifibered-span-diagram)
      ( refl-htpy)
      ( refl-htpy)
      ( coherence-square-cocone-flattening-pushout Q f g c)
  coherence-cube-flattening-lemma-equifibered-span-diagram (s , t) =
    ( ap-id
      ( coherence-square-cocone-flattening-equifibered-span-diagram f g c P Q e
        ( s , t))) ∙
    ( triangle-eq-pair-Σ Q
      ( coherence-square-cocone f g c s)
      ( coherence-map-flattening-equifibered-span-diagram f g c P Q e s t)) ∙
    ( ap
      ( eq-pair-Σ (coherence-square-cocone f g c s) refl ∙_)
      ( inv
        ( ( right-unit) ∙
          ( compute-ap-map-Σ-map-base-eq-pair-Σ
            ( vertical-map-cocone f g c)
            ( Q)
            ( refl)
            ( coherence-map-flattening-equifibered-span-diagram
              f g c P Q e s t)))))

  abstract
    flattening-lemma-equifibered-span-diagram :
      flattening-lemma-equifibered-span-diagram-statement f g c P Q e
    flattening-lemma-equifibered-span-diagram up-c =
      universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
        ( vertical-map-span-flattening-pushout Q f g c)
        ( horizontal-map-span-flattening-pushout Q f g c)
        ( horizontal-map-cocone-flattening-pushout Q f g c)
        ( vertical-map-cocone-flattening-pushout Q f g c)
        ( vertical-map-span-flattening-equifibered-span-diagram P)
        ( horizontal-map-span-flattening-equifibered-span-diagram P)
        ( horizontal-map-cocone-flattening-equifibered-span-diagram f g c P Q e)
        ( vertical-map-cocone-flattening-equifibered-span-diagram f g c P Q e)
        ( equiv-source-cube-flattening-equifibered-span-diagram)
        ( equiv-tot
          ( left-equiv-equiv-equifibered-span-diagram
            ( P)
            ( equifibered-span-diagram-family-cocone-span-diagram c Q)
            ( e)))
        ( equiv-tot
          ( right-equiv-equiv-equifibered-span-diagram
            ( P)
            ( equifibered-span-diagram-family-cocone-span-diagram c Q)
            ( e)))
        ( id-equiv)
        ( coherence-square-cocone-flattening-equifibered-span-diagram
          f g c P Q e)
        ( refl-htpy)
        ( back-right-coherence-cube-flattening-lemma-equifibered-span-diagram)
        ( refl-htpy)
        ( refl-htpy)
        ( coherence-square-cocone-flattening-pushout Q f g c)
        ( coherence-cube-flattening-lemma-equifibered-span-diagram)
        ( flattening-lemma-pushout Q f g c up-c)
```

## See also

- [Mather's second cube theorem](synthetic-homotopy-theory.mathers-second-cube-theorem.md)
  is the [unstraightened](foundation.type-duality.md) version of the flattening
  lemma for pushouts.
