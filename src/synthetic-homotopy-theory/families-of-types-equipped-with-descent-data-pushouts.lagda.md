# Families of types equipped with descent data for pushouts

```agda
module
  synthetic-homotopy-theory.families-of-types-equipped-with-descent-data-pushouts
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.descent-property-families-of-types-pushouts
open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
```

</details>

## Idea

A {{#concept "family of types equipped with descent data" Disambiguation="pushouts"}} for the [pushout](synthetic-homotopy-theory.universal-property-pushouts.md) over a [cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` with codomain `X` under a [span diagram](foundation.span-diagrams.md) `𝒮` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X
        i
```

consists of a type family `Y` over `X`, the [structure of a type family](synthetic-homotopy-theory.families-of-types-pushouts.md) `P` over the span diagram `𝒮` and an [equivalence of structures of type families for pushouts](synthetic-homotopy-theory.equivalences-families-of-types-pushouts.md)

```text
  e : P ≃ descent-data-type-family 𝒮 c Y.
```

By the [descent property](synthetic-homotopy-theory.descent-property-families-of-types-pushouts.md) for pushouts it follows that for any type family equipped with descent data `(Y , P , e)` over a _pushout_, the types of [pairs](foundation.dependent-pair-types.md) `(Y , e)` and `(P , e)` are [contractible](foundation-core.contractible-types.md).

## Definitions

### Type families equipped with descent data

```agda
module _
  {l1 l2 l3 l4 : Level} (l5 l6 : Level) (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  where

  family-with-descent-data-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  family-with-descent-data-pushout =
    Σ ( X → UU l5)
      ( λ Y →
        Σ ( structure-type-family-pushout l6 s)
          ( λ P →
            equiv-structure-type-family-pushout s P
              ( descent-data-type-family-pushout s c Y)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (Y : family-with-descent-data-pushout l5 l6 s c)
  where

  type-family-family-with-descent-data-pushout : X → UU l5
  type-family-family-with-descent-data-pushout = pr1 Y

  structure-type-family-family-with-descent-data-pushout :
    structure-type-family-pushout l6 s
  structure-type-family-family-with-descent-data-pushout =
    pr1 (pr2 Y)

  left-type-family-family-with-descent-data-pushout :
    domain-span-diagram s → UU l6
  left-type-family-family-with-descent-data-pushout =
    left-type-family-structure-type-family-pushout s
      structure-type-family-family-with-descent-data-pushout

  right-type-family-family-with-descent-data-pushout :
    codomain-span-diagram s → UU l6
  right-type-family-family-with-descent-data-pushout =
    right-type-family-structure-type-family-pushout s
      structure-type-family-family-with-descent-data-pushout

  matching-equiv-family-with-descent-data-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-family-with-descent-data-pushout
      ( left-map-span-diagram s x) ≃
    right-type-family-family-with-descent-data-pushout
      ( right-map-span-diagram s x)
  matching-equiv-family-with-descent-data-pushout =
    matching-equiv-structure-type-family-pushout s
      structure-type-family-family-with-descent-data-pushout

  map-matching-equiv-family-with-descent-data-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-family-with-descent-data-pushout
      ( left-map-span-diagram s x) →
    right-type-family-family-with-descent-data-pushout
      ( right-map-span-diagram s x)
  map-matching-equiv-family-with-descent-data-pushout =
    map-matching-equiv-structure-type-family-pushout s
      structure-type-family-family-with-descent-data-pushout

  descent-data-type-family-family-with-descent-data-pushout :
    structure-type-family-pushout l5 s
  descent-data-type-family-family-with-descent-data-pushout =
    descent-data-type-family-pushout s c
      type-family-family-with-descent-data-pushout

  equiv-structure-type-family-family-with-descent-data-pushout :
    equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
  equiv-structure-type-family-family-with-descent-data-pushout =
    pr2 (pr2 Y)

  left-equiv-structure-type-family-family-with-descent-data-pushout :
    equiv-left-type-family-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
  left-equiv-structure-type-family-family-with-descent-data-pushout =
    left-equiv-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( equiv-structure-type-family-family-with-descent-data-pushout)

  map-left-equiv-structure-type-family-family-with-descent-data-pushout :
    (a : domain-span-diagram s) →
    left-type-family-family-with-descent-data-pushout a →
    type-family-family-with-descent-data-pushout
      ( left-map-cocone-span-diagram s c a)
  map-left-equiv-structure-type-family-family-with-descent-data-pushout =
    map-left-equiv-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( equiv-structure-type-family-family-with-descent-data-pushout)

  right-equiv-structure-type-family-family-with-descent-data-pushout :
    equiv-right-type-family-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
  right-equiv-structure-type-family-family-with-descent-data-pushout =
    right-equiv-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( equiv-structure-type-family-family-with-descent-data-pushout)

  map-right-equiv-structure-type-family-family-with-descent-data-pushout :
    (b : codomain-span-diagram s) →
    right-type-family-family-with-descent-data-pushout b →
    type-family-family-with-descent-data-pushout
      ( right-map-cocone-span-diagram s c b)
  map-right-equiv-structure-type-family-family-with-descent-data-pushout =
    map-right-equiv-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( equiv-structure-type-family-family-with-descent-data-pushout)

  coherence-equiv-structure-type-family-family-with-descent-data-pushout :
    coherence-square-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( left-equiv-structure-type-family-family-with-descent-data-pushout)
      ( right-equiv-structure-type-family-family-with-descent-data-pushout)
  coherence-equiv-structure-type-family-family-with-descent-data-pushout =
    coherence-equiv-structure-type-family-pushout s
      ( structure-type-family-family-with-descent-data-pushout)
      ( descent-data-type-family-family-with-descent-data-pushout)
      ( equiv-structure-type-family-family-with-descent-data-pushout)
```
