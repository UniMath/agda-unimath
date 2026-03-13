# Precomplete short maps on pseudometric spaces

```agda
module metric-spaces.precomplete-short-maps-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

A [short maps](metric-spaces.short-maps-pseudometric-spaces.md) `f : P → M` from
a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P` in a
[metric space](metric-spaces.metric-spaces.md) `M` is called
{{#concept "precomplete" Disambiguation="from a pseudometric space to a metric space" Agda=is-precomplete-short-map-Pseudometric-Space}}
if all
[images](metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces.md)
of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in `P` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`M`.

Any **precomplete** short map `f : P → M`
[extends](orthogonal-factorization-systems.extensions-maps.md) along the unit
map of
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md):

```text
    P
    |  \
  κ |    \ f
    |      \
    ∨    g   ∨
   C P ------> M
```

Composition of short maps preserves precomplete short maps: if `f : P → M` is
**precomplete**,

- for any pseudometric space `Q` and short map `h : Q → P`, `f ∘ h : Q → M` is
  **precomplete**;
- for any metric space `N` and short map `h : M → N`, `h ∘ f : P → N` is
  **precomplete**.

## Definitions

### Precomposition of short maps by the unit map of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space g =
    comp-short-map-Pseudometric-Space
      ( P)
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( g)
      ( short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P)
```

### The property of being a precomplete short map from a pseudometric space to a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-precomplete-prop-short-map-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-precomplete-prop-short-map-Pseudometric-Space =
    Π-Prop
      ( cauchy-approximation-Pseudometric-Space P)
      ( is-convergent-prop-cauchy-approximation-Metric-Space M ∘
        map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( f))

  is-precomplete-short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-precomplete-short-map-Pseudometric-Space =
    type-Prop is-precomplete-prop-short-map-Pseudometric-Space

  is-prop-is-precomplete-short-map-Pseudometric-Space :
    is-prop is-precomplete-short-map-Pseudometric-Space
  is-prop-is-precomplete-short-map-Pseudometric-Space =
    is-prop-type-Prop is-precomplete-prop-short-map-Pseudometric-Space
```

### The type of precomplete short maps from a pseudometric space to a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomplete-short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  precomplete-short-map-Pseudometric-Space =
    type-subtype
      ( is-precomplete-prop-short-map-Pseudometric-Space P M)

  short-map-precomplete-short-map-Pseudometric-Space :
    precomplete-short-map-Pseudometric-Space →
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  short-map-precomplete-short-map-Pseudometric-Space = pr1

  map-precomplete-short-map-Pseudometric-Space :
    precomplete-short-map-Pseudometric-Space →
    map-Pseudometric-Space P (pseudometric-Metric-Space M)
  map-precomplete-short-map-Pseudometric-Space f =
    map-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( short-map-precomplete-short-map-Pseudometric-Space f)

  is-precomplete-short-map-precomplete-short-map-Pseudometric-Space :
    (f : precomplete-short-map-Pseudometric-Space) →
    is-precomplete-short-map-Pseudometric-Space P M
      ( short-map-precomplete-short-map-Pseudometric-Space f)
  is-precomplete-short-map-precomplete-short-map-Pseudometric-Space = pr2
```

## Properties

### A precomplete short map extends to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-short-map-Pseudometric-Space P M)
  where

  map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space u =
    limit-is-convergent-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( u))
      ( is-precomplete-short-map-precomplete-short-map-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( u))

  sim-const-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    (u : cauchy-approximation-Pseudometric-Space P) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( u)))
  sim-const-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( u))
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( u))
      ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
        ( M)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-precomplete-short-map-Pseudometric-Space P M f)
          ( u))
        ( is-precomplete-short-map-precomplete-short-map-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( u)))

  is-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  is-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    d u v Nuv =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-unit-cauchy-pseudocompletion-Metric-Space M)
      ( d)
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( u))
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( v))
      ( preserves-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        { map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-precomplete-short-map-Pseudometric-Space P M f)
          ( u)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( u))}
        { map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-precomplete-short-map-Pseudometric-Space P M f)
          ( v)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( v))}
        ( sim-const-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( u))
        ( sim-const-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( v))
        ( d)
        ( is-short-map-short-map-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( short-map-precomplete-short-map-Pseudometric-Space P M f))
          ( d)
          ( u)
          ( v)
          ( Nuv)))

  short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  pr1
    short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
  pr2
    short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space

  is-extension-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-extension-of-map
      ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P)
      ( map-precomplete-short-map-Pseudometric-Space P M f)
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  is-extension-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    x =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
      ( map-precomplete-short-map-Pseudometric-Space P M f x)
      ( map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
      ( is-limit-const-cauchy-approximation-Metric-Space M
        ( map-precomplete-short-map-Pseudometric-Space P M f x))
      ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
        ( M)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-precomplete-short-map-Pseudometric-Space P M f)
          ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
        ( is-precomplete-short-map-precomplete-short-map-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x)))
```

### Composition preserves precomplete short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-short-map-Pseudometric-Space P M)
  where abstract

  is-precomplete-left-comp-precomplete-short-map-Pseudometric-Space :
    {l l' : Level} →
    (Q : Pseudometric-Space l l') →
    (g : short-map-Pseudometric-Space Q P) →
    is-precomplete-short-map-Pseudometric-Space
      ( Q)
      ( M)
      ( comp-short-map-Pseudometric-Space
        ( Q)
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( g))
  is-precomplete-left-comp-precomplete-short-map-Pseudometric-Space Q g u =
    is-precomplete-short-map-precomplete-short-map-Pseudometric-Space
      ( P)
      ( M)
      ( f)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space Q P g u)

  is-precomplete-right-comp-precomplete-short-map-Pseudometric-Space :
    {l l' : Level} →
    (N : Metric-Space l l') →
    (g : short-map-Metric-Space M N) →
    is-precomplete-short-map-Pseudometric-Space
      ( P)
      ( N)
      ( comp-short-map-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( pseudometric-Metric-Space N)
        ( g)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f))
  is-precomplete-right-comp-precomplete-short-map-Pseudometric-Space N g u =
    is-convergent-map-short-map-convergent-cauchy-approximation-Metric-Space
      ( M)
      ( N)
      ( g)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( u))
      ( is-precomplete-short-map-precomplete-short-map-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( u))
```

### Short maps from the Cauchy pseudocompletions restrict to precomplete short maps

#### Values of short maps from cauchy pseudocompletions into metric spaces are limits

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( g :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  ( u : cauchy-approximation-Pseudometric-Space P)
  where abstract

  sim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g))
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-short-map-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-Metric-Space M)
          ( g)
          ( u)))
  sim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    tr
      ( sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( g))
          ( u)))
      ( naturality-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g)
        ( u))
      ( preserves-sim-map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( cauchy-pseudocompletion-Metric-Space M)
        ( short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-Metric-Space M)
          ( g))
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P)
          ( u))
        ( map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( u))
        ( sim-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( u)))

  is-lim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g))
        ( u))
      ( map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g)
        ( u))
  is-lim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-limit-sim-const-cauchy-approximation-Metric-Space M
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g))
        ( u))
      ( map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g)
        ( u))
      ( sim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

#### Restrictions to short maps from Cauchy pseudocompletions are precomplete

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( g :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  where

  is-precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space :
    is-precomplete-short-map-Pseudometric-Space P M
      ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M g)
  is-precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
    u =
    ( ( map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g)
        ( u)) ,
      ( is-lim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( g)
        ( u)))
```

#### The precomplete restriction of a short map from a Cauchy pseudocompletion in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    precomplete-short-map-Pseudometric-Space P M
  precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
    g =
    ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M g ,
      is-precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( g))
```

### Short maps from the Cauchy pseudocompletion are the extension of their restrictions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where abstract

  is-section-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    ( short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ∘
    ( precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)) ~
    ( id)
  is-section-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    g =
    eq-htpy-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g)))
      ( g)
      ( refl-htpy)

  is-retraction-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    ( precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ∘
    ( short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ~
    ( id)
  is-retraction-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    f =
    eq-type-subtype
      ( is-precomplete-prop-short-map-Pseudometric-Space P M)
      ( eq-htpy-map-short-map-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f)))
        ( short-map-precomplete-short-map-Pseudometric-Space P M f)
        ( inv-htpy
          ( is-extension-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f))))

  is-equiv-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-equiv
      ( short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
  is-equiv-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-equiv-is-invertible
      ( precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( is-section-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-retraction-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

### The equivalence between precomplete short maps and short maps from the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    precomplete-short-map-Pseudometric-Space P M ≃
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  pr1
    equiv-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
  pr2
    equiv-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-equiv-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
```
