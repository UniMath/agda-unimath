# Functorialiy of metric quotients of pseudometric spaces and short maps

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.functoriality-short-maps-metric-quotients-of-pseudometric-spaces where
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

open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

Postcomposition with the natural
[isometry](metric-spaces.isometries-pseudometric-spaces.md) from a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `Q` into its
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)

```text
q : Q → [Q]
```

maps [short maps](metric-spaces.short-maps-pseudometric-spaces.md) `f : P → Q`
from a pseudometric spaces `P` to short maps `q ∘ f : P → [Q]`. By the
[universal property of metric quotients and short maps](metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces.md),
these factor as short maps `g : [P] → [Q]`. This action preserves the identity
and composition of short maps.

It is the
{{#concept "functorial action" Disambiguation="of metric quotients on short maps" Agda=hom-metric-quotient-short-map-Pseudometric-Space}}
of metric quotients on short maps.

## Definitions

### Postcomposition of short maps by the metric quotient isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  where

  postcomp-short-map-metric-quotient-Pseudometric-Space :
    short-map-Pseudometric-Space P Q →
    short-map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
  postcomp-short-map-metric-quotient-Pseudometric-Space =
    comp-short-map-Pseudometric-Space
      ( P)
      ( Q)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( short-map-metric-quotient-Pseudometric-Space Q)
```

### Action of metric quotients on short maps between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space P Q)
  where

  hom-metric-quotient-short-map-Pseudometric-Space :
    short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
  hom-metric-quotient-short-map-Pseudometric-Space =
    short-map-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space Q)
      ( postcomp-short-map-metric-quotient-Pseudometric-Space P Q f)

  map-hom-metric-quotient-short-map-Pseudometric-Space :
    map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
  map-hom-metric-quotient-short-map-Pseudometric-Space =
    map-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
      ( hom-metric-quotient-short-map-Pseudometric-Space)
```

## Properties

### The action of metric quotients on short maps is natural

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (Q : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space P Q)
  where

  coh-square-map-hom-metric-quotient-short-map-Pseudometric-Space :
    ( map-hom-metric-quotient-short-map-Pseudometric-Space P Q f ∘
      map-metric-quotient-Pseudometric-Space P) ~
    ( map-metric-quotient-Pseudometric-Space Q ∘
      map-short-map-Pseudometric-Space P Q f)
  coh-square-map-hom-metric-quotient-short-map-Pseudometric-Space =
    htpy-map-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space Q)
      ( postcomp-short-map-metric-quotient-Pseudometric-Space P Q f)

  coh-square-hom-short-map-metric-quotiemt-Pseudometric-Space :
    comp-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( hom-metric-quotient-short-map-Pseudometric-Space P Q f)
      ( short-map-metric-quotient-Pseudometric-Space P) ＝
    comp-short-map-Pseudometric-Space
      ( P)
      ( Q)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( short-map-metric-quotient-Pseudometric-Space Q)
      ( f)
  coh-square-hom-short-map-metric-quotiemt-Pseudometric-Space =
    eq-htpy-map-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space Q)
      ( comp-short-map-Pseudometric-Space
        ( P)
        ( pseudometric-metric-quotient-Pseudometric-Space P)
        ( pseudometric-metric-quotient-Pseudometric-Space Q)
        ( hom-metric-quotient-short-map-Pseudometric-Space P Q f)
        ( short-map-metric-quotient-Pseudometric-Space P))
      ( comp-short-map-Pseudometric-Space
        ( P)
        ( Q)
        ( pseudometric-metric-quotient-Pseudometric-Space Q)
        ( short-map-metric-quotient-Pseudometric-Space Q)
        ( f))
      ( coh-square-map-hom-metric-quotient-short-map-Pseudometric-Space)
```

### The action on short maps of metric quotients preserves the identity

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where abstract

  coh-short-map-id-short-map-metric-quotient-Pseudometric-Space :
    coh-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space P)
      ( short-map-metric-quotient-Pseudometric-Space P)
  pr1 coh-short-map-id-short-map-metric-quotient-Pseudometric-Space =
    id-short-map-Metric-Space (metric-quotient-Pseudometric-Space P)
  pr2 coh-short-map-id-short-map-metric-quotient-Pseudometric-Space = refl-htpy

  htpy-id-hom-id-short-map-metric-quotient-Pseudometric-Space :
    ( map-hom-metric-quotient-short-map-Pseudometric-Space P P
      ( id-short-map-Pseudometric-Space P)) ~
    ( id)
  htpy-id-hom-id-short-map-metric-quotient-Pseudometric-Space =
    all-htpy-coh-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space P)
      ( short-map-metric-quotient-Pseudometric-Space P)
      ( coh-short-map-id-short-map-metric-quotient-Pseudometric-Space)

  preserves-id-hom-metric-quotient-short-map-Pseudometric-Space :
    hom-metric-quotient-short-map-Pseudometric-Space P P
      ( id-short-map-Pseudometric-Space P) ＝
    id-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
  preserves-id-hom-metric-quotient-short-map-Pseudometric-Space =
    eq-htpy-map-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space P)
      ( hom-metric-quotient-short-map-Pseudometric-Space P P
        ( id-short-map-Pseudometric-Space P))
      ( id-short-map-Metric-Space (metric-quotient-Pseudometric-Space P))
      ( htpy-id-hom-id-short-map-metric-quotient-Pseudometric-Space)
```

### The action on short maps of metric quotients preserves composition

```agda
module _
  {lp lp' lq lq' lr lr' : Level}
  (P : Pseudometric-Space lp lp')
  (Q : Pseudometric-Space lq lq')
  (R : Pseudometric-Space lr lr')
  (g : short-map-Pseudometric-Space Q R)
  (f : short-map-Pseudometric-Space P Q)
  where abstract

  coh-short-map-comp-short-map-metric-quotient-Pseudometric-Space :
    coh-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space R)
      ( postcomp-short-map-metric-quotient-Pseudometric-Space
        ( P)
        ( R)
        ( comp-short-map-Pseudometric-Space P Q R g f))
  pr1 coh-short-map-comp-short-map-metric-quotient-Pseudometric-Space =
    comp-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space Q)
      ( metric-quotient-Pseudometric-Space R)
      ( hom-metric-quotient-short-map-Pseudometric-Space Q R g)
      ( hom-metric-quotient-short-map-Pseudometric-Space P Q f)
  pr2 coh-short-map-comp-short-map-metric-quotient-Pseudometric-Space =
    ( map-hom-metric-quotient-short-map-Pseudometric-Space Q R g) ·l
    ( coh-square-map-hom-metric-quotient-short-map-Pseudometric-Space P Q f) ∙h
    ( coh-square-map-hom-metric-quotient-short-map-Pseudometric-Space Q R g) ·r
    ( map-short-map-Pseudometric-Space P Q f)

  htpy-comp-map-hom-comp-short-map-metric-quotient-Pseudometric-Space :
    ( map-hom-metric-quotient-short-map-Pseudometric-Space P R
      ( comp-short-map-Pseudometric-Space P Q R g f)) ~
    ( map-hom-metric-quotient-short-map-Pseudometric-Space Q R g ∘
      map-hom-metric-quotient-short-map-Pseudometric-Space P Q f)
  htpy-comp-map-hom-comp-short-map-metric-quotient-Pseudometric-Space =
    all-htpy-coh-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-quotient-Pseudometric-Space R)
      ( postcomp-short-map-metric-quotient-Pseudometric-Space
        ( P)
        ( R)
        ( comp-short-map-Pseudometric-Space P Q R g f))
      ( coh-short-map-comp-short-map-metric-quotient-Pseudometric-Space)

  preserves-comp-hom-metric-quotient-short-map-Pseudometric-Space :
      ( hom-metric-quotient-short-map-Pseudometric-Space P R
        ( comp-short-map-Pseudometric-Space P Q R g f)) ＝
      ( comp-short-map-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( metric-quotient-Pseudometric-Space Q)
        ( metric-quotient-Pseudometric-Space R)
        ( hom-metric-quotient-short-map-Pseudometric-Space Q R g)
        ( hom-metric-quotient-short-map-Pseudometric-Space P Q f))
  preserves-comp-hom-metric-quotient-short-map-Pseudometric-Space =
    eq-htpy-map-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-quotient-Pseudometric-Space R)
      ( hom-metric-quotient-short-map-Pseudometric-Space P R
        ( comp-short-map-Pseudometric-Space P Q R g f))
      ( comp-short-map-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( metric-quotient-Pseudometric-Space Q)
        ( metric-quotient-Pseudometric-Space R)
        ( hom-metric-quotient-short-map-Pseudometric-Space Q R g)
        ( hom-metric-quotient-short-map-Pseudometric-Space P Q f))
      ( htpy-comp-map-hom-comp-short-map-metric-quotient-Pseudometric-Space)
```
