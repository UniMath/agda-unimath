# Flattening families of types over pushouts

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module synthetic-homotopy-theory.flattening-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.spans
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.descent-property-families-of-types-pushouts
open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-equipped-with-descent-data-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
open import synthetic-homotopy-theory.sections-families-of-types-pushouts
```

</details>

## Idea

Consider the
[structure of a type family](synthetic-homotopy-theory.families-of-types-pushouts.md)
`(P , Q , e)` over a [span diagram](foundation.span-diagrams.md) `𝒮`. The
{{#concept "flattening" Disambiguation="families over span diagrams"}} of
`(P , Q , e)` is the span diagram

```text
  Σ (a : A), P a <-- Σ (s : S), P (f s) --> Σ (s : S), Q (g s) --> Σ (b : B), Q b
```

where the map in the middle is the
[map on total spaces](foundation.functoriality-dependent-pair-types.md) of the
[family of equivalences](foundation.families-of-equivalences.md) `e`.

In the case where the structure of a family over a span diagram is obtained from
a type family `P` over the codomain of a
[cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md), we obtain a
cocone on the flattening of that structure. This will be called the
{{#concept "flattening" Disambiguation="families over cocones under span diagrams"}}.

The flattening span diagrams and cocones introduced in this file will be used to
state and prove the
[flattening lemma](synthetic-homotopy-theory.flattening-lemma.md).

## Definitions

### Flattening of the structure of a type family over a span diagram

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  where

  spanning-type-flattening-structure-type-family-pushout : UU (l3 ⊔ l4)
  spanning-type-flattening-structure-type-family-pushout =
    Σ ( spanning-type-span-diagram 𝒮)
      ( ( left-type-family-structure-type-family-pushout 𝒮 P) ∘
        ( left-map-span-diagram 𝒮))

  domain-flattening-structure-type-family-pushout : UU (l1 ⊔ l4)
  domain-flattening-structure-type-family-pushout =
    Σ ( domain-span-diagram 𝒮)
      ( left-type-family-structure-type-family-pushout 𝒮 P)

  codomain-flattening-structure-type-family-pushout : UU (l2 ⊔ l4)
  codomain-flattening-structure-type-family-pushout =
    Σ ( codomain-span-diagram 𝒮)
      ( right-type-family-structure-type-family-pushout 𝒮 P)

  left-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    domain-flattening-structure-type-family-pushout
  left-map-flattening-structure-type-family-pushout =
    map-Σ-map-base
      ( left-map-span-diagram 𝒮)
      ( left-type-family-structure-type-family-pushout 𝒮 P)

  right-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    codomain-flattening-structure-type-family-pushout
  right-map-flattening-structure-type-family-pushout =
    map-Σ
      ( right-type-family-structure-type-family-pushout 𝒮 P)
      ( right-map-span-diagram 𝒮)
      ( map-matching-equiv-structure-type-family-pushout 𝒮 P)

  span-flattening-structure-type-family-pushout :
    span
      ( l3 ⊔ l4)
      ( domain-flattening-structure-type-family-pushout)
      ( codomain-flattening-structure-type-family-pushout)
  pr1 span-flattening-structure-type-family-pushout =
    spanning-type-flattening-structure-type-family-pushout
  pr1 (pr2 span-flattening-structure-type-family-pushout) =
    left-map-flattening-structure-type-family-pushout
  pr2 (pr2 span-flattening-structure-type-family-pushout) =
    right-map-flattening-structure-type-family-pushout

  span-diagram-flattening-structure-type-family-pushout :
    span-diagram (l1 ⊔ l4) (l2 ⊔ l4) (l3 ⊔ l4)
  span-diagram-flattening-structure-type-family-pushout =
    make-span-diagram
      left-map-flattening-structure-type-family-pushout
      right-map-flattening-structure-type-family-pushout
```

### Flattening families over cocones equipped with structure of families over span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (P : structure-type-family-pushout l5 𝒮)
  (Q : X → UU l5)
  (e :
    equiv-structure-type-family-pushout 𝒮 P
      ( descent-data-type-family-pushout 𝒮 c Q))
  where

  left-map-cocone-flattening-structure-type-family-pushout :
    domain-flattening-structure-type-family-pushout 𝒮 P → Σ X Q
  left-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( left-map-cocone-span-diagram 𝒮 c)
      ( map-left-equiv-equiv-structure-type-family-pushout 𝒮 P
        ( descent-data-type-family-pushout 𝒮 c Q)
        ( e))

  right-map-cocone-flattening-structure-type-family-pushout :
    codomain-flattening-structure-type-family-pushout 𝒮 P → Σ X Q
  right-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( right-map-cocone-span-diagram 𝒮 c)
      ( map-right-equiv-equiv-structure-type-family-pushout 𝒮 P
        ( descent-data-type-family-pushout 𝒮 c Q)
        ( e))

  coherence-square-cocone-flattening-structure-type-family-pushout :
    coherence-square-maps
      ( right-map-flattening-structure-type-family-pushout 𝒮 P)
      ( left-map-flattening-structure-type-family-pushout 𝒮 P)
      ( right-map-cocone-flattening-structure-type-family-pushout)
      ( left-map-cocone-flattening-structure-type-family-pushout)
  coherence-square-cocone-flattening-structure-type-family-pushout =
    htpy-map-Σ Q
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( λ x →
        map-left-equiv-equiv-structure-type-family-pushout 𝒮 P
          ( descent-data-type-family-pushout 𝒮 c Q)
          ( e)
          ( left-map-span-diagram 𝒮 x))
      ( λ x →
        inv-htpy
          ( coherence-equiv-structure-type-family-pushout 𝒮 P
            ( descent-data-type-family-pushout 𝒮 c Q)
            ( e)
            ( x)))

  cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( Σ X Q)
  pr1 cocone-flattening-structure-type-family-pushout =
    left-map-cocone-flattening-structure-type-family-pushout
  pr1 (pr2 cocone-flattening-structure-type-family-pushout) =
    right-map-cocone-flattening-structure-type-family-pushout
  pr2 (pr2 cocone-flattening-structure-type-family-pushout) =
    coherence-square-cocone-flattening-structure-type-family-pushout
```

### Flattening families of types over pushouts

Consider a type family `P` over the codomain `X` of a cocone `c` under a span
diagram `A <- S -> B`. The descent data of `P` then yields the
[structure of a type family](synthetic-homotopy-theory.structure-type-family-pushout.md)
over a pushout. The flattening of `P` consists of the span diagram and the
cocone as displayed in the following commuting square:

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x).
```

Note that this is defined as a special case of the flattening of the structure
of a type family over a pushout, by first taking the descent data of `P` and
then flattening.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X) (P : X → UU l5)
  where

  spanning-type-flattening-type-family-pushout : UU (l3 ⊔ l5)
  spanning-type-flattening-type-family-pushout =
    spanning-type-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  domain-flattening-type-family-pushout : UU (l1 ⊔ l5)
  domain-flattening-type-family-pushout =
    domain-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  codomain-flattening-type-family-pushout : UU (l2 ⊔ l5)
  codomain-flattening-type-family-pushout =
    codomain-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  left-map-flattening-type-family-pushout :
    spanning-type-flattening-type-family-pushout →
    domain-flattening-type-family-pushout
  left-map-flattening-type-family-pushout =
    left-map-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  right-map-flattening-type-family-pushout :
    spanning-type-flattening-type-family-pushout →
    codomain-flattening-type-family-pushout
  right-map-flattening-type-family-pushout =
    right-map-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  span-flattening-type-family-pushout :
    span
      ( l3 ⊔ l5)
      ( domain-flattening-type-family-pushout)
      ( codomain-flattening-type-family-pushout)
  span-flattening-type-family-pushout =
    span-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  span-diagram-flattening-type-family-pushout :
    span-diagram (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-diagram-flattening-type-family-pushout =
    span-diagram-flattening-structure-type-family-pushout 𝒮
      ( descent-data-type-family-pushout 𝒮 c P)

  left-map-cocone-flattening-type-family-pushout :
    domain-flattening-type-family-pushout → Σ X P
  left-map-cocone-flattening-type-family-pushout =
    left-map-cocone-flattening-structure-type-family-pushout 𝒮 c
      ( descent-data-type-family-pushout 𝒮 c P)
      ( P)
      ( id-equiv-structure-type-family-pushout 𝒮
        ( descent-data-type-family-pushout 𝒮 c P))

  right-map-cocone-flattening-type-family-pushout :
    codomain-flattening-type-family-pushout → Σ X P
  right-map-cocone-flattening-type-family-pushout =
    right-map-cocone-flattening-structure-type-family-pushout 𝒮 c
      ( descent-data-type-family-pushout 𝒮 c P)
      ( P)
      ( id-equiv-structure-type-family-pushout 𝒮
        ( descent-data-type-family-pushout 𝒮 c P))

  coherence-square-cocone-flattening-type-family-pushout :
    coherence-square-maps
      ( right-map-flattening-type-family-pushout)
      ( left-map-flattening-type-family-pushout)
      ( right-map-cocone-flattening-type-family-pushout)
      ( left-map-cocone-flattening-type-family-pushout)
  coherence-square-cocone-flattening-type-family-pushout =
    coherence-square-cocone-flattening-structure-type-family-pushout 𝒮 c
      ( descent-data-type-family-pushout 𝒮 c P)
      ( P)
      ( id-equiv-structure-type-family-pushout 𝒮
        ( descent-data-type-family-pushout 𝒮 c P))

  cocone-flattening-type-family-pushout :
    cocone-span-diagram span-diagram-flattening-type-family-pushout (Σ X P)
  cocone-flattening-type-family-pushout =
    cocone-flattening-structure-type-family-pushout 𝒮 c
      ( descent-data-type-family-pushout 𝒮 c P)
      ( P)
      ( id-equiv-structure-type-family-pushout 𝒮
        ( descent-data-type-family-pushout 𝒮 c P))
```

## Properties

### The flattening span diagrams of equivalent structures of type families of a pushout are equivalent

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 𝒮)
  (Q : structure-type-family-pushout l5 𝒮)
  (e : equiv-structure-type-family-pushout 𝒮 P Q)
  where

  left-equiv-flattening-equiv-structure-type-family-pushout :
    domain-flattening-structure-type-family-pushout 𝒮 P ≃
    domain-flattening-structure-type-family-pushout 𝒮 Q
  left-equiv-flattening-equiv-structure-type-family-pushout =
    equiv-tot (left-equiv-equiv-structure-type-family-pushout 𝒮 P Q e)

  left-map-flattening-equiv-structure-type-family-pushout :
    domain-flattening-structure-type-family-pushout 𝒮 P →
    domain-flattening-structure-type-family-pushout 𝒮 Q
  left-map-flattening-equiv-structure-type-family-pushout =
    map-equiv left-equiv-flattening-equiv-structure-type-family-pushout

  right-equiv-flattening-equiv-structure-type-family-pushout :
    codomain-flattening-structure-type-family-pushout 𝒮 P ≃
    codomain-flattening-structure-type-family-pushout 𝒮 Q
  right-equiv-flattening-equiv-structure-type-family-pushout =
    equiv-tot (right-equiv-equiv-structure-type-family-pushout 𝒮 P Q e)

  right-map-flattening-equiv-structure-type-family-pushout :
    codomain-flattening-structure-type-family-pushout 𝒮 P →
    codomain-flattening-structure-type-family-pushout 𝒮 Q
  right-map-flattening-equiv-structure-type-family-pushout =
    map-equiv right-equiv-flattening-equiv-structure-type-family-pushout

  spanning-equiv-flattening-equiv-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout 𝒮 P ≃
    spanning-type-flattening-structure-type-family-pushout 𝒮 Q
  spanning-equiv-flattening-equiv-structure-type-family-pushout =
    equiv-tot
      ( ( left-equiv-equiv-structure-type-family-pushout 𝒮 P Q e) ∘
        ( left-map-span-diagram 𝒮))

  spanning-map-flattening-equiv-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout 𝒮 P →
    spanning-type-flattening-structure-type-family-pushout 𝒮 Q
  spanning-map-flattening-equiv-structure-type-family-pushout =
    map-equiv spanning-equiv-flattening-equiv-structure-type-family-pushout

  left-square-equiv-flattening-equiv-structure-type-family-pushout :
    coherence-square-maps
      ( spanning-map-flattening-equiv-structure-type-family-pushout)
      ( left-map-flattening-structure-type-family-pushout 𝒮 P)
      ( left-map-flattening-structure-type-family-pushout 𝒮 Q)
      ( left-map-flattening-equiv-structure-type-family-pushout)
  left-square-equiv-flattening-equiv-structure-type-family-pushout =
    refl-htpy

  right-square-equiv-flattening-equiv-structure-type-family-pushout :
    coherence-square-maps
      ( spanning-map-flattening-equiv-structure-type-family-pushout)
      ( right-map-flattening-structure-type-family-pushout 𝒮 P)
      ( right-map-flattening-structure-type-family-pushout 𝒮 Q)
      ( right-map-flattening-equiv-structure-type-family-pushout)
  right-square-equiv-flattening-equiv-structure-type-family-pushout (s , p) =
    eq-pair-Σ refl (coherence-equiv-structure-type-family-pushout 𝒮 P Q e s p)

  equiv-span-flattening-equiv-structure-type-family-pushout :
    equiv-span
      ( concat-span
        ( span-flattening-structure-type-family-pushout 𝒮 P)
        ( left-map-flattening-equiv-structure-type-family-pushout)
        ( right-map-flattening-equiv-structure-type-family-pushout))
      ( span-flattening-structure-type-family-pushout 𝒮 Q)
  pr1 equiv-span-flattening-equiv-structure-type-family-pushout =
    spanning-equiv-flattening-equiv-structure-type-family-pushout
  pr1 (pr2 equiv-span-flattening-equiv-structure-type-family-pushout) =
    left-square-equiv-flattening-equiv-structure-type-family-pushout
  pr2 (pr2 equiv-span-flattening-equiv-structure-type-family-pushout) =
    right-square-equiv-flattening-equiv-structure-type-family-pushout

  equiv-span-diagram-flattening-equiv-structure-type-family-pushout :
    equiv-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 Q)
  pr1 equiv-span-diagram-flattening-equiv-structure-type-family-pushout =
    left-equiv-flattening-equiv-structure-type-family-pushout
  pr1 (pr2 equiv-span-diagram-flattening-equiv-structure-type-family-pushout) =
    right-equiv-flattening-equiv-structure-type-family-pushout
  pr2 (pr2 equiv-span-diagram-flattening-equiv-structure-type-family-pushout) =
    equiv-span-flattening-equiv-structure-type-family-pushout
```

### Computation of cocones under the flattening span diagram of the structure of a type family of a pushout

Consider the structure of a type family `(P , Q , e)` over a span diagram
`A <- S -> B`, with flattening span diagram `𝒯`

```text
  Σ (a : A), P a <-- Σ (s : S), P (f s) --> Σ (s : S), Q (g s) --> Σ (b : B), Q b.
```

Furthermore, consider a type `X`, a type family `Y` over `X`, a cocone `c` on
`𝒮` with codomain `X` and a dependent cocone `d` on `𝒯` over `c` with codomain
`Y`. Then there is a commuting square

```text
                          ev-pair
  ((Σ (x : X), Y x) → Z) ---------> ((x : X) → Y x → Z)
             |                               |
  cocone-map |                               | dependent-cocone-map
             V         ≃                     V
        cocone 𝒯 Z ---------> dependent-cocone 𝒮 c (λ x → Y x → Z)
```

in which the bottom map is an equivalence. Here, the type of cocones on `𝒯` is
the type of triples

```text
  i' : (Σ (a : A), P a) → Z
  j' : (Σ (b : B), Q b) → Z
  H' : ((s , p) : Σ (s : S), P (f s)) → i' (f s , p) ＝ j' (g s , e s p),
```

and the type of dependent cocones on `𝒮` over `c` is the type of triples

```text
  i" : (a : A) → Y (i a) → Z
  j" : (b : B) → Y (j b) → Z
  H" : (s : S) (y : Y (i (f s))) → i" (f s) y ＝ j" (g s) (tr Y (H s) y)
```

**Proof.** Since the span diagram `𝒯` is equivalent to the flattening span
diagram `Σ 𝒮 Y`

```text
  Σ (a : A), Y (i a) <----- Σ (s : S), Y (i (f s)) -----> Σ (b : B), Y (j b)
```

we obtain a commuting square

```text
                           id
  ((Σ (x : X), Y x) → Z) -----> ((Σ (x : x), Y x) → Z)
               |                             |
    cocone-map |                             | cocone-map
               V             ≃               V
          cocone 𝒯 Z -----------------> cocone (Σ 𝒮 Y) Z
```

Furthermore, it is straightforward to see that we have a commuting square

```text
  ((Σ (x : X), Y x) → Z) -------------> ((x : X) → Y x → Z)
               |                                 |
    cocone-map |                                 | dependent-cocone-map
               V                ≃                V
          cocone (Σ 𝒮 Y) Z ----------> dependent-cocone 𝒮 (λ x → Y x → Z)
```

The claim now follows by pasting these two commuting squares.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (Y : family-with-descent-data-pushout l5 l6 𝒮 c)
  (Z : UU l7)
  where

  span-diagram-flattening-family-with-descent-data-pushout :
    span-diagram (l1 ⊔ l6) (l2 ⊔ l6) (l3 ⊔ l6)
  span-diagram-flattening-family-with-descent-data-pushout =
    span-diagram-flattening-structure-type-family-pushout 𝒮
      ( structure-type-family-family-with-descent-data-pushout 𝒮 c Y)

  span-diagram-flattening-family-with-descent-data-pushout' :
    span-diagram (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-diagram-flattening-family-with-descent-data-pushout' =
    span-diagram-flattening-type-family-pushout 𝒮 c
      ( type-family-family-with-descent-data-pushout 𝒮 c Y)

  cocone-flattening-family-with-descent-data-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  cocone-flattening-family-with-descent-data-pushout =
    cocone-span-diagram
      ( span-diagram-flattening-family-with-descent-data-pushout)
      ( Z)

  cocone-flattening-family-with-descent-data-pushout' :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l5 ⊔ l7)
  cocone-flattening-family-with-descent-data-pushout' =
    cocone-span-diagram
      ( span-diagram-flattening-family-with-descent-data-pushout')
      ( Z)

  dependent-cocone-flattening-family-with-descent-data-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l5 ⊔ l7)
  dependent-cocone-flattening-family-with-descent-data-pushout =
    dependent-cocone-span-diagram 𝒮 c
      ( λ s → type-family-family-with-descent-data-pushout 𝒮 c Y s → Z)

  compute-cocone-flattening-family-with-descent-data-pushout' :
    cocone-flattening-family-with-descent-data-pushout' ≃
    dependent-cocone-flattening-family-with-descent-data-pushout
  compute-cocone-flattening-family-with-descent-data-pushout' =
    equiv-Σ _
      ( equiv-ev-pair)
      ( λ f →
        equiv-Σ _
          ( equiv-ev-pair)
          ( λ g →
            ( equiv-Π-equiv-family
              ( λ s →
                ( inv-equiv equiv-funext) ∘e
                ( equiv-Π _
                  {!!}
                  {!!}))) ∘e
            ( equiv-ev-pair)))

  compute-cocone-flattening-family-with-descent-data-pushout :
    cocone-flattening-family-with-descent-data-pushout ≃
    dependent-cocone-flattening-family-with-descent-data-pushout
  compute-cocone-flattening-family-with-descent-data-pushout =
    ( ( equiv-structure-section-type-family-pushout 𝒮
        {!!}
        ( descent-data-type-family-pushout 𝒮 c
          ( λ x → type-family-family-with-descent-data-pushout 𝒮 c Y x → Z))
        {!!})) ∘e
    ( {!!} ∘e
      ( equiv-Σ _
      ( equiv-ev-pair)
        ( λ _ → equiv-Σ _ equiv-ev-pair (λ _ → equiv-ev-pair))))

{-
    equiv-Σ _
      ( ( inv-equiv
          ( equiv-Π-equiv-family
            ( λ a →
              equiv-precomp
                ( left-equiv-family-with-descent-data-pushout 𝒮 c Y a)
                ( Z)))) ∘e
        ( equiv-ev-pair))
      ( λ α →
        equiv-Σ _
          ( ( inv-equiv
              ( equiv-Π-equiv-family
                ( λ b →
                  equiv-precomp
                    ( right-equiv-family-with-descent-data-pushout 𝒮 c Y b)
                    ( Z)))) ∘e
            ( equiv-ev-pair))
          ( λ β →
            ( equiv-Π-equiv-family
              ( λ s →
                {!!})) ∘e
            ( equiv-ev-pair))) -}
```

```text
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s) (X : UU l5)
  where

  structure-cocone-flattening-structure-type-family-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  structure-cocone-flattening-structure-type-family-pushout =
    Σ ( (a : domain-span-diagram 𝒮) →
        left-type-family-structure-type-family-pushout 𝒮 P a → X)
      ( λ p →
        Σ ( (b : codomain-span-diagram 𝒮) →
            right-type-family-structure-type-family-pushout 𝒮 P b → X)
          ( λ q →
            (s : spanning-type-span-diagram 𝒮) →
            (t : spanning-type-family-structure-type-family-pushout 𝒮 P s) →
            p (left-map-span-diagram 𝒮 s) t ＝
            q ( right-map-span-diagram 𝒮 s)
              ( map-matching-equiv-structure-type-family-pushout 𝒮 P s t)))

  compute-cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( X) ≃
    structure-cocone-flattening-structure-type-family-pushout
  compute-cocone-flattening-structure-type-family-pushout =
    equiv-Σ _
      ( equiv-ev-pair)
      ( λ _ → equiv-Σ _ equiv-ev-pair (λ _ → equiv-ev-pair))

  map-compute-cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout 𝒮 P)
      ( X) →
    structure-cocone-flattening-structure-type-family-pushout
  map-compute-cocone-flattening-structure-type-family-pushout =
    map-equiv compute-cocone-flattening-structure-type-family-pushout

  triangle-compute-cocone-flattening-structure-type-family-pushout :
    coherence-triangle-maps
      {!!}
      {!!}
      {!!}
  triangle-compute-cocone-flattening-structure-type-family-pushout = {!!}

{-
  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map-span-diagram 𝒮 c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-type-family-pushout Y ∘ ind-Σ)
-}
```
