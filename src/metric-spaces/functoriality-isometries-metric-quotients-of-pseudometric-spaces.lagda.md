# Functoriality of metric quotients of pseudometric spaces and isometries

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.functoriality-isometries-metric-quotients-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces
open import metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

Postcomposition with the
[unit map of metric quotients](metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces.md),

```text
  q : Q → [Q]
```

maps isometries `f : P → Q` from a pseudometric spaces `P` to isometries
`q ∘ f : P → [Q]`. By the
[universal property of metric quotients and isometries](metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces.md),
these factor as isometries `q⋆f : [P] → [Q]`. This action preserves the identity
and composition of isometries and induce commutative diagrams

```text
       f         g
  P ------> Q ------> R
  |         |         |
  |         |         |
  |         |         |
  v         v         v
 [P] ----> [Q] ----> [R]
      q⋆f       q⋆g
```

This is the
{{#concept "functorial action" Disambiguation="of metric quotients on isometries" Agda=isometry-metric-quotient-Pseudometric-Space}}
of metric quotients on isometries.

## Definitions

### Postcomposition of isometries by the unit isometry of metric quotients

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  where

  postcomp-isometry-unit-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space P Q →
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
  postcomp-isometry-unit-metric-quotient-Pseudometric-Space =
    comp-isometry-Pseudometric-Space
      ( P)
      ( Q)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( isometry-unit-metric-quotient-Pseudometric-Space Q)
```

### Action of metric quotients on isometries between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  where

  isometry-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space P Q →
    isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
  isometry-metric-quotient-Pseudometric-Space f =
    isometry-exten-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space Q)
      ( postcomp-isometry-unit-metric-quotient-Pseudometric-Space P Q f)

  short-map-isometry-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space P Q →
    short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
  short-map-isometry-metric-quotient-Pseudometric-Space =
    short-map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q) ∘
    isometry-metric-quotient-Pseudometric-Space

  map-isometry-metric-quotient-Pseudometric-Space :
    isometry-Pseudometric-Space P Q →
    map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
  map-isometry-metric-quotient-Pseudometric-Space =
    map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q) ∘
    isometry-metric-quotient-Pseudometric-Space
```

## Properties

### The action of metric quotients on isometries is natural

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space P Q)
  where

  coh-square-map-isometry-metric-quotient-Pseudometric-Space :
    ( map-isometry-metric-quotient-Pseudometric-Space P Q f ∘
      map-unit-metric-quotient-Pseudometric-Space P) ~
    ( map-unit-metric-quotient-Pseudometric-Space Q ∘
      map-isometry-Pseudometric-Space P Q f)
  coh-square-map-isometry-metric-quotient-Pseudometric-Space =
    is-extension-exten-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space Q)
      ( postcomp-isometry-unit-metric-quotient-Pseudometric-Space P Q f)

  coh-square-isometry-metric-quotient-Pseudometric-Space :
    comp-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( isometry-metric-quotient-Pseudometric-Space P Q f)
      ( isometry-unit-metric-quotient-Pseudometric-Space P) ＝
    comp-isometry-Pseudometric-Space
      ( P)
      ( Q)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( isometry-unit-metric-quotient-Pseudometric-Space Q)
      ( f)
  coh-square-isometry-metric-quotient-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( comp-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-metric-quotient-Pseudometric-Space P)
        ( pseudometric-metric-quotient-Pseudometric-Space Q)
        ( isometry-metric-quotient-Pseudometric-Space P Q f)
        ( isometry-unit-metric-quotient-Pseudometric-Space P))
      ( comp-isometry-Pseudometric-Space
        ( P)
        ( Q)
        ( pseudometric-metric-quotient-Pseudometric-Space Q)
        ( isometry-unit-metric-quotient-Pseudometric-Space Q)
        ( f))
      ( coh-square-map-isometry-metric-quotient-Pseudometric-Space)
```

### The action on isometries of metric quotients preserves the identity

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where abstract

  exten-id-isometry-metric-quotient-Pseudometric-Space :
    extension-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space P)
      ( isometry-unit-metric-quotient-Pseudometric-Space P)
  pr1 exten-id-isometry-metric-quotient-Pseudometric-Space =
    id-isometry-Metric-Space (metric-quotient-Pseudometric-Space P)
  pr2 exten-id-isometry-metric-quotient-Pseudometric-Space = refl-htpy

  htpy-id-isometry-metric-quotient-Pseudometric-Space :
    ( map-isometry-metric-quotient-Pseudometric-Space P P
      ( id-isometry-Pseudometric-Space P)) ~
    ( id)
  htpy-id-isometry-metric-quotient-Pseudometric-Space =
    all-htpy-map-extension-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space P)
      ( isometry-unit-metric-quotient-Pseudometric-Space P)
      ( exten-id-isometry-metric-quotient-Pseudometric-Space)

  preserves-id-isometry-metric-quotient-Pseudometric-Space :
    isometry-metric-quotient-Pseudometric-Space P P
      ( id-isometry-Pseudometric-Space P) ＝
    id-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
  preserves-id-isometry-metric-quotient-Pseudometric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space P)
      ( htpy-id-isometry-metric-quotient-Pseudometric-Space)
```

### The action on isometries of metric quotients preserves composition

```agda
module _
  {lp lp' lq lq' lr lr' : Level}
  (P : Pseudometric-Space lp lp')
  (Q : Pseudometric-Space lq lq')
  (R : Pseudometric-Space lr lr')
  (g : isometry-Pseudometric-Space Q R)
  (f : isometry-Pseudometric-Space P Q)
  where abstract

  exten-comp-isometry-metric-quotient-Pseudometric-Space :
    extension-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space R)
      ( postcomp-isometry-unit-metric-quotient-Pseudometric-Space
        ( P)
        ( R)
        ( comp-isometry-Pseudometric-Space P Q R g f))
  pr1 exten-comp-isometry-metric-quotient-Pseudometric-Space =
    comp-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
      ( metric-quotient-Pseudometric-Space R)
      ( isometry-metric-quotient-Pseudometric-Space Q R g)
      ( isometry-metric-quotient-Pseudometric-Space P Q f)
  pr2 exten-comp-isometry-metric-quotient-Pseudometric-Space =
    ( map-isometry-metric-quotient-Pseudometric-Space Q R g) ·l
    ( coh-square-map-isometry-metric-quotient-Pseudometric-Space P Q f) ∙h
    ( coh-square-map-isometry-metric-quotient-Pseudometric-Space Q R g) ·r
    ( map-isometry-Pseudometric-Space P Q f)

  htpy-comp-map-metric-quotient-isometry-Pseudometric-Space :
    ( map-isometry-metric-quotient-Pseudometric-Space P R
      ( comp-isometry-Pseudometric-Space P Q R g f)) ~
    ( map-isometry-metric-quotient-Pseudometric-Space Q R g ∘
      map-isometry-metric-quotient-Pseudometric-Space P Q f)
  htpy-comp-map-metric-quotient-isometry-Pseudometric-Space =
    all-htpy-map-extension-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space R)
      ( postcomp-isometry-unit-metric-quotient-Pseudometric-Space P R
        ( comp-isometry-Pseudometric-Space P Q R g f))
      ( exten-comp-isometry-metric-quotient-Pseudometric-Space)

  preserves-comp-isometry-metric-quotient-Pseudometric-Space :
      ( isometry-metric-quotient-Pseudometric-Space P R
        ( comp-isometry-Pseudometric-Space P Q R g f)) ＝
      ( comp-isometry-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( metric-quotient-Pseudometric-Space Q)
        ( metric-quotient-Pseudometric-Space R)
        ( isometry-metric-quotient-Pseudometric-Space Q R g)
        ( isometry-metric-quotient-Pseudometric-Space P Q f))
  preserves-comp-isometry-metric-quotient-Pseudometric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space R)
      ( htpy-comp-map-metric-quotient-isometry-Pseudometric-Space)
```
