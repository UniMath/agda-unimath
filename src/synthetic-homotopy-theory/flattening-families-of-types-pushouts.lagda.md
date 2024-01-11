# Flattening families of types over pushouts

```agda
module synthetic-homotopy-theory.flattening-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.families-of-types-pushouts
```

</details>

## Idea

Consider the [structure of a type family](synthetic-homotopy-theory.families-of-types-pushouts.md) `(P , Q , e)` over a [span diagram](foundation.span-diagrams.md) `s`. The {{#concept "flattening" Disambiguation="families over span diagrams"}} of `(P , Q , e)` is the span diagram

```text
  Σ (a : A), P a <-- Σ (s : S), P (f s) --> Σ (s : S), Q (g s) --> Σ (b : B), Q b
```

where the map in the middle is the [map on total spaces](foundation.functoriality-dependent-pair-types.md) of the [family of equivalences](foundation.families-of-equivalences.md) `e`.

In the case where the structure of a family over a span diagram is obtained from a type family `P` over the codomain of a [cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md), we obtain a cocone on the flattening of that structure. This will be called the {{#concept "flattening" Disambiguation="families over cocones under span diagrams"}}.

The flattening span diagrams and cocones introduced in this file will be used to state and prove the [flattening lemma](synthetic-homotopy-theory.flattening-lemma.md).

## Definitions

### Flattening of the structure of a type family over a span diagram

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  spanning-type-flattening-structure-type-family-pushout : UU (l3 ⊔ l4)
  spanning-type-flattening-structure-type-family-pushout =
    Σ ( spanning-type-span-diagram s)
      ( ( left-type-family-structure-type-family-pushout s P) ∘
        ( left-map-span-diagram s))

  domain-flattening-structure-type-family-pushout : UU (l1 ⊔ l4)
  domain-flattening-structure-type-family-pushout =
    Σ ( domain-span-diagram s)
      ( left-type-family-structure-type-family-pushout s P)

  codomain-flattening-structure-type-family-pushout : UU (l2 ⊔ l4)
  codomain-flattening-structure-type-family-pushout =
    Σ ( codomain-span-diagram s)
      ( right-type-family-structure-type-family-pushout s P)

  left-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    domain-flattening-structure-type-family-pushout
  left-map-flattening-structure-type-family-pushout =
    map-Σ-map-base
      ( left-map-span-diagram s)
      ( left-type-family-structure-type-family-pushout s P)

  right-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    codomain-flattening-structure-type-family-pushout
  right-map-flattening-structure-type-family-pushout =
    map-Σ
      ( right-type-family-structure-type-family-pushout s P)
      ( right-map-span-diagram s)
      ( map-matching-equiv-structure-type-family-pushout s P)

  flattening-structure-type-family-pushout :
    span-diagram (l1 ⊔ l4) (l2 ⊔ l4) (l3 ⊔ l4)
  flattening-structure-type-family-pushout =
    make-span-diagram
      left-map-flattening-structure-type-family-pushout
      right-map-flattening-structure-type-family-pushout
```

### Flattening families over cocones equipped with structure of families over span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (P : structure-type-family-pushout l5 s)
  (Q : X → UU l5)
  (e :
    equiv-structure-type-family-pushout s P
      ( descent-data-type-family-pushout s c Q))
  where

  left-map-cocone-flattening-structure-type-family-pushout :
    domain-flattening-structure-type-family-pushout s P → Σ X Q
  left-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( left-map-cocone-span-diagram s c)
      ( map-left-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  right-map-cocone-flattening-structure-type-family-pushout :
    codomain-flattening-structure-type-family-pushout s P → Σ X Q
  right-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( right-map-cocone-span-diagram s c)
      ( map-right-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  coherence-square-cocone-flattening-structure-type-family-pushout :
    coherence-square-maps
      ( right-map-flattening-structure-type-family-pushout s P)
      ( left-map-flattening-structure-type-family-pushout s P)
      ( right-map-cocone-flattening-structure-type-family-pushout)
      ( left-map-cocone-flattening-structure-type-family-pushout)
  coherence-square-cocone-flattening-structure-type-family-pushout =
    htpy-map-Σ Q
      ( coherence-square-cocone-span-diagram s c)
      ( λ x →
        map-left-equiv-equiv-structure-type-family-pushout s P
          ( descent-data-type-family-pushout s c Q)
          ( e)
          ( left-map-span-diagram s x))
      ( λ x →
        inv-htpy
          ( coherence-equiv-structure-type-family-pushout s P
            ( descent-data-type-family-pushout s c Q)
            ( e)
            ( x)))

  cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( flattening-structure-type-family-pushout s P)
      ( Σ X Q)
  pr1 cocone-flattening-structure-type-family-pushout =
    left-map-cocone-flattening-structure-type-family-pushout
  pr1 (pr2 cocone-flattening-structure-type-family-pushout) =
    right-map-cocone-flattening-structure-type-family-pushout
  pr2 (pr2 cocone-flattening-structure-type-family-pushout) =
    coherence-square-cocone-flattening-structure-type-family-pushout
```
