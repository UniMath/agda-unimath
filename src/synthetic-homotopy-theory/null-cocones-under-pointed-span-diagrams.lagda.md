# Null cocones under pointed span diagrams

```agda
module synthetic-homotopy-theory.null-cocones-under-pointed-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.constant-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
```

</details>

## Idea

The {{#concept "null cocone" Disambiguation="pointed span diagram}} under a
[pointed span diagram](structured-types.pointed-span-diagrams.md) `𝒮` given by

```text
      f       g
  A <---- S ----> B
```

with codomain `X` is the
[cocone](synthetic-homotopy-theory.cocones-under-pointed-span-diagrams.md) under
`𝒮` consisting of the
[constant pointed maps](structured-types.constant-pointed-maps.md) `A →∗ X` and
`B →∗ X` and the canonical homotopy witnessing that the square of pointed maps

```text
        g
    S -----> B
    |        |
  f |        | const
    ∨        ∨
    A -----> X
      const
```

[commutes](structured-types.commuting-squares-pointed-maps.md). The null cocone
under `𝒮` provides a canonical pointing of the type `cocone-Pointed-Type f g`.

## Definitions

### Null cocones under pointed span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2}
  {B : Pointed-Type l3}
  (f : S →∗ A) (g : S →∗ B)
  (X : Pointed-Type l4)
  where

  left-pointed-map-null-cocone-Pointed-Type : A →∗ X
  left-pointed-map-null-cocone-Pointed-Type = constant-pointed-map A X

  right-pointed-map-null-cocone-Pointed-Type : B →∗ X
  right-pointed-map-null-cocone-Pointed-Type = constant-pointed-map B X

  htpy-coherence-square-null-cocone-Pointed-Type :
    coherence-square-maps
      ( map-pointed-map g)
      ( map-pointed-map f)
      ( map-constant-pointed-map B X)
      ( map-constant-pointed-map A X)
  htpy-coherence-square-null-cocone-Pointed-Type = refl-htpy

  coherence-point-coherence-square-null-cocone-Pointed-Type :
    coherence-point-unpointed-htpy-pointed-Π
      ( constant-pointed-map A X ∘∗ f)
      ( constant-pointed-map B X ∘∗ g)
      ( htpy-coherence-square-null-cocone-Pointed-Type)
  coherence-point-coherence-square-null-cocone-Pointed-Type =
    right-whisker-concat
      ( ( ap-const
          ( point-Pointed-Type X)
          ( preserves-point-pointed-map f)) ∙
        ( inv
          ( ap-const
            ( point-Pointed-Type X)
            ( preserves-point-pointed-map g))))
      ( refl)

  coherence-square-null-cocone-Pointed-Type :
    coherence-square-pointed-maps g f
      ( right-pointed-map-null-cocone-Pointed-Type)
      ( left-pointed-map-null-cocone-Pointed-Type)
  pr1 coherence-square-null-cocone-Pointed-Type =
    htpy-coherence-square-null-cocone-Pointed-Type
  pr2 coherence-square-null-cocone-Pointed-Type =
    coherence-point-coherence-square-null-cocone-Pointed-Type

  null-cocone-Pointed-Type : cocone-Pointed-Type f g X
  pr1 null-cocone-Pointed-Type =
    left-pointed-map-null-cocone-Pointed-Type
  pr1 (pr2 null-cocone-Pointed-Type) =
    right-pointed-map-null-cocone-Pointed-Type
  pr2 (pr2 null-cocone-Pointed-Type) =
    coherence-square-null-cocone-Pointed-Type
```

### The pointed type of cocones under pointed span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2}
  {B : Pointed-Type l3}
  (f : S →∗ A) (g : S →∗ B)
  (X : Pointed-Type l4)
  where

  type-cocone-pointed-type-Pointed-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cocone-pointed-type-Pointed-Type = cocone-Pointed-Type f g X

  cocone-pointed-type-Pointed-Type : Pointed-Type (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 cocone-pointed-type-Pointed-Type = type-cocone-pointed-type-Pointed-Type
  pr2 cocone-pointed-type-Pointed-Type = null-cocone-Pointed-Type f g X
```
