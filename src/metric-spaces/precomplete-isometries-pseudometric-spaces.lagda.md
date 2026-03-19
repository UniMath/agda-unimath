# Precomplete isometries on pseudometric spaces

```agda
module metric-spaces.precomplete-isometries-pseudometric-spaces where
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
open import metric-spaces.expansive-maps-pseudometric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precomplete-short-maps-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

An [isometry](metric-spaces.isometries-pseudometric-spaces.md) `f : P → M` from
a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P` in a
[metric space](metric-spaces.metric-spaces.md) `M` is called
{{#concept "precomplete" Disambiguation="from a pseudometric space to a metric space" Agda=is-precomplete-isometry-Pseudometric-Space}}
if all
[images](metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces.md)
of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in `P` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`M`.

Any **precomplete** isometry `f : P → M`
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

Composition of isometries preserves precomplete isometries: if `f : P → M` is
**precomplete**,

- for any pseudometric space `Q` and isometry `h : Q → P`, `f ∘ h : Q → M` is
  **precomplete**;
- for any metric space `N` and isometry `h : M → N`, `h ∘ f : P → N` is
  **precomplete**.

## Definitions

### Precomposition of isometries by the unit map of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space g =
    comp-isometry-Pseudometric-Space
      ( P)
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( g)
      ( isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P)
```

### The property of being a precomplete short map from a pseudometric space to a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-precomplete-prop-isometry-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-precomplete-prop-isometry-Pseudometric-Space =
    Π-Prop
      ( cauchy-approximation-Pseudometric-Space P)
      ( is-convergent-prop-cauchy-approximation-Metric-Space M ∘
        map-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( f))

  is-precomplete-isometry-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-precomplete-isometry-Pseudometric-Space =
    type-Prop is-precomplete-prop-isometry-Pseudometric-Space

  is-prop-is-precomplete-isometry-Pseudometric-Space :
    is-prop is-precomplete-isometry-Pseudometric-Space
  is-prop-is-precomplete-isometry-Pseudometric-Space =
    is-prop-type-Prop is-precomplete-prop-isometry-Pseudometric-Space
```

### The type of precomplete isometries from a pseudometric space to a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomplete-isometry-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  precomplete-isometry-Pseudometric-Space =
    type-subtype
      ( is-precomplete-prop-isometry-Pseudometric-Space P M)

  isometry-precomplete-isometry-Pseudometric-Space :
    precomplete-isometry-Pseudometric-Space →
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  isometry-precomplete-isometry-Pseudometric-Space = pr1

  map-precomplete-isometry-Pseudometric-Space :
    precomplete-isometry-Pseudometric-Space →
    map-Pseudometric-Space P (pseudometric-Metric-Space M)
  map-precomplete-isometry-Pseudometric-Space f =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( isometry-precomplete-isometry-Pseudometric-Space f)

  is-precomplete-isometry-precomplete-isometry-Pseudometric-Space :
    (f : precomplete-isometry-Pseudometric-Space) →
    is-precomplete-isometry-Pseudometric-Space P M
      ( isometry-precomplete-isometry-Pseudometric-Space f)
  is-precomplete-isometry-precomplete-isometry-Pseudometric-Space = pr2
```

### Homotopies between precomplete isometries

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f g : precomplete-isometry-Pseudometric-Space P M)
  where

  htpy-map-precomplete-isometry-Pseudometric-Space : UU (l1 ⊔ l1')
  htpy-map-precomplete-isometry-Pseudometric-Space =
    map-precomplete-isometry-Pseudometric-Space P M f ~
    map-precomplete-isometry-Pseudometric-Space P M g
```

## Properties

### Homotopic precomplete isometries are equal

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  {f g : precomplete-isometry-Pseudometric-Space P M}
  where

  eq-htpy-map-precomplete-isometry-Pseudometric-Space :
    htpy-map-precomplete-isometry-Pseudometric-Space P M f g →
    f ＝ g
  eq-htpy-map-precomplete-isometry-Pseudometric-Space =
    eq-type-subtype (is-precomplete-prop-isometry-Pseudometric-Space P M) ∘
    eq-htpy-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( isometry-precomplete-isometry-Pseudometric-Space P M f)
      ( isometry-precomplete-isometry-Pseudometric-Space P M g)

  eq-inv-htpy-map-precomplete-isometry-Pseudometric-Space :
    htpy-map-precomplete-isometry-Pseudometric-Space P M g f →
    f ＝ g
  eq-inv-htpy-map-precomplete-isometry-Pseudometric-Space =
    eq-htpy-map-precomplete-isometry-Pseudometric-Space ∘ inv-htpy
```

### The precomplete short map induced by a precompelete isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-isometry-Pseudometric-Space P M)
  where

  precomplete-short-map-precomplete-isometry-Pseudometric-Space :
    precomplete-short-map-Pseudometric-Space P M
  pr1 precomplete-short-map-precomplete-isometry-Pseudometric-Space =
    short-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( isometry-precomplete-isometry-Pseudometric-Space P M f)
  pr2 precomplete-short-map-precomplete-isometry-Pseudometric-Space =
    is-precomplete-isometry-precomplete-isometry-Pseudometric-Space P M f
```

### A precomplete short map extends to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-isometry-Pseudometric-Space P M)
  where

  map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space u =
    limit-is-convergent-cauchy-approximation-Metric-Space
      ( M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( u))
      ( is-precomplete-isometry-precomplete-isometry-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( u))

  sim-const-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    (u : cauchy-approximation-Pseudometric-Space P) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( u)))
  sim-const-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( u))
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( u))
      ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
        ( M)
        ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( isometry-precomplete-isometry-Pseudometric-Space P M f)
          ( u))
        ( is-precomplete-isometry-precomplete-isometry-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( u)))

  is-short-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-short-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( precomplete-short-map-precomplete-isometry-Pseudometric-Space P M f)

  is-expansive-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-expansive-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-expansive-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    d u v Nuv =
    is-expansive-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f))
      ( d)
      ( u)
      ( v)
      ( reflects-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        { map-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( isometry-precomplete-isometry-Pseudometric-Space P M f)
          ( u)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( u))}
        { map-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( isometry-precomplete-isometry-Pseudometric-Space P M f)
          ( v)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( v))}
        ( sim-const-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( u))
        ( sim-const-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( v))
        ( d)
        ( preserves-neighborhoods-map-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( isometry-unit-cauchy-pseudocompletion-Metric-Space M)
          ( d)
          ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( u))
          ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( v))
          ( Nuv)))

  is-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-isometry-is-expansive-is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-short-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-expansive-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    isometry-is-expansive-is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-short-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-expansive-map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  is-extension-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-extension-of-map
      ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P)
      ( map-precomplete-isometry-Pseudometric-Space P M f)
      ( map-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-extension-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-extension-short-map-exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( precomplete-short-map-precomplete-isometry-Pseudometric-Space P M f)
```

### Composition preserves precomplete isometries

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-isometry-Pseudometric-Space P M)
  where abstract

  is-precomplete-left-comp-precomplete-isometry-Pseudometric-Space :
    {l l' : Level} →
    (Q : Pseudometric-Space l l') →
    (g : isometry-Pseudometric-Space Q P) →
    is-precomplete-isometry-Pseudometric-Space
      ( Q)
      ( M)
      ( comp-isometry-Pseudometric-Space
        ( Q)
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( g))
  is-precomplete-left-comp-precomplete-isometry-Pseudometric-Space Q g u =
    is-precomplete-isometry-precomplete-isometry-Pseudometric-Space
      ( P)
      ( M)
      ( f)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space Q P g u)

  is-precomplete-right-comp-precomplete-isometry-Pseudometric-Space :
    {l l' : Level} →
    (N : Metric-Space l l') →
    (g : isometry-Metric-Space M N) →
    is-precomplete-isometry-Pseudometric-Space
      ( P)
      ( N)
      ( comp-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( pseudometric-Metric-Space N)
        ( g)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f))
  is-precomplete-right-comp-precomplete-isometry-Pseudometric-Space N g u =
    is-convergent-map-isometry-is-convergent-cauchy-approximation-Metric-Space
      ( M)
      ( N)
      ( g)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( u))
      ( is-precomplete-isometry-precomplete-isometry-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( u))
```

### Isometries from the Cauchy pseudocompletions restrict to precomplete isometries

#### Values of isometries from cauchy pseudocompletions into metric spaces are limits

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  ( u : cauchy-approximation-Pseudometric-Space P)
  where abstract

  sim-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g))
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-Metric-Space M)
          ( g)
          ( u)))
  sim-map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    sim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g))
      ( u)

  is-lim-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g))
        ( u))
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g)
        ( u))
  is-lim-map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    is-lim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g))
      ( u)
```

#### Restrictions of isometries from Cauchy pseudocompletions are precomplete

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  where

  is-precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space :
    is-precomplete-isometry-Pseudometric-Space P M
      ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M g)
  is-precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-precomplete-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g))
```

#### The precomplete restriction of a short map from a Cauchy pseudocompletion in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    precomplete-isometry-Pseudometric-Space P M
  precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
    g =
    ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M g ,
      is-precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( g))
```

### Isometries from the Cauchy pseudocompletion are the extension of their restrictions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where abstract

  is-section-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    ( isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ∘
    ( precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)) ~
    ( id)
  is-section-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    g =
    eq-htpy-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( g)))
      ( g)
      ( refl-htpy)

  is-retraction-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    ( precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ∘
    ( isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)) ~
    ( id)
  is-retraction-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    f =
    eq-inv-htpy-map-precomplete-isometry-Pseudometric-Space
      ( P)
      ( M)
      ( is-extension-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))

  is-equiv-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-equiv
      ( isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
  is-equiv-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-equiv-is-invertible
      ( precomplete-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( is-section-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( is-retraction-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
```

### The equivalence between precomplete isometries and isometries from the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    precomplete-isometry-Pseudometric-Space P M ≃
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  pr1
    equiv-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
  pr2
    equiv-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-equiv-isometry-exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
```

### An isometry homotopic to a precomplete isometry is precomplete

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f g : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-precomplete-htpy-map-isometry-Pseudometric-Space :
    htpy-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( f)
      ( g) →
    is-precomplete-isometry-Pseudometric-Space P M f →
    is-precomplete-isometry-Pseudometric-Space P M g
  is-precomplete-htpy-map-isometry-Pseudometric-Space =
    is-precomplete-htpy-map-short-map-Pseudometric-Space P M
      ( short-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f)
      ( short-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) g)
```
