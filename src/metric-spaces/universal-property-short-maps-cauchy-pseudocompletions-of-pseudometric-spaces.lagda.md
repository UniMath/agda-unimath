# Universal property of Cauchy pseudocompletions of pseudometric spaces and short maps into metric spaces

```agda
module metric-spaces.universal-property-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
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

Given a [metric space](metric-spaces.metric-spaces.md) `M` and a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `P`, precomposition
with the unit of the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md)

```text
  κ : P → C P
```

maps [short maps](metric-spaces.short-maps-pseudometric-spaces.md) `g : C P → M`
to short maps `g ∘ κ : P → M`. For any
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
`u : C P`, its
[image](metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces.md)
`C(g ∘ κ) u : C M`
[converges](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) to
`g u` so `g` is determined by its restriction to `P` and `g ∘ κ` is
[precomplete](metric-spaces.precomplete-short-maps-pseudometric-spaces.md).

Conversely, if a short map `f : P → M`,
[extends](orthogonal-factorization-systems.extensions-maps.md) along `κ`, i.e.,
there exists a short map `g : C P → M` such that

```text
  f ~ g ∘ κ
```

then such an
{{#concept "extension" Disambiguation="of short maps on pseudometric spaces along κ" Agda=extension-short-map-cauchy-pseudocompletion-Pseudometric-Space}}
is unique and exists if and only if `f` is precomplete.

It follows that the type of
{{#concept "extensible short maps" Disambiguation="from a pseudometric space along κ" Agda=extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space}}
is [equivalent](foundation.equivalences.md) to type of precomplete short maps.

Equivalently, the Cauchy pseudocompletion satisfies the
{{#concept "universal property" Disambiguation="of Cauchy pseudocompletions and precomplete short maps" Agda=is-contr-extension-precomplete-short-map-Pseudometric-Space}}
of Cauchy precompletions and precomplete short maps: for any precomplete short
map `f : P → M` from a pseudometric space in a metric space, there
[uniquely exists](foundation.uniqueness-quantification.md) an extension of `f`
along `κ`.

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

### Extensions of short maps along the unit map of Cauchy pseudocompletions

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  ( g :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  where

  is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l1')
  is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-extension-of-map
      ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P)
      ( map-short-map-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
      ( map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g))

  is-prop-is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-prop
      is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
  is-prop-is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-prop-Π
      ( λ x →
        is-set-type-Metric-Space M
          ( map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)
            ( x))
          ( map-short-map-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( pseudometric-Metric-Space M)
            ( g)
            ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x)))

  is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    ( is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space ,
      is-prop-is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    Σ ( short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M))
      ( is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f)
  where

  short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    pr1 g

  precomp-short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space)

  map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space)

  htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f
      ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    pr2 g
```

### Extensible short maps along the unit map of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    Σ ( short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
      ( extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space P M)
  where

  short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    = pr1 f

  exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
  exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    = pr2 f

  short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    pr1
      exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space

  htpy-map-exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    htpy-map-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)
      ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M
        ( short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space))
  htpy-map-exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    pr2
      exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
```

## Properties

### A short map from the Cauchy pseudocompletion extends its precomposition by the unit map

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

  extension-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M g)
  extension-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space =
    ( g , refl-htpy)
```

### Precomplete short maps extend to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-short-map-Pseudometric-Space P M)
  where

  exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( short-map-precomplete-short-map-Pseudometric-Space P M f)
  pr1 exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    short-map-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( f)
  pr2 exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-extension-short-map-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( f)
```

### Values of short maps from cauchy pseudocompletions into metric spaces are limits

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

### The values of extensions of short maps are limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f)
  (u : cauchy-approximation-Pseudometric-Space P)
  where abstract

  sim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)
          ( u)))
  sim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    inv-tr
      ( sim-Pseudometric-Space'
        ( cauchy-pseudocompletion-Metric-Space M)
        ( map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f)
            ( g)
            ( u))))
      ( htpy-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( precomp-short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( u))
      ( sim-map-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
        ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( u))

  is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
  is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-limit-sim-const-cauchy-approximation-Metric-Space M
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
      ( sim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

### All extensions of a short map to the Cauchy pseudocompletion are homotopic

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  all-htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    ( g h :
      extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f) →
    map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f g ~
    map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f h
  all-htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    g h u =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
      ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( h)
        ( u))
      ( is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
      ( is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( h)
        ( u))
```

### Extensions of short maps are unique

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  all-eq-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    ( g h :
      extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f) →
    ( g ＝ h)
  all-eq-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space g h =
    eq-type-subtype
      ( is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
      ( eq-htpy-map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( h))
        ( all-htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)
          ( h)))

  is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-prop
      ( extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f)
  is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-prop-all-elements-equal
      all-eq-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
```

### The property of being a short map extensible to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    ( extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f ,
      is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
```

### A short map extends to the Cauchy pseudocompletion if and only if it is precomplete

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f →
    is-precomplete-short-map-Pseudometric-Space P M f
  is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    g u =
    ( map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u) ,
      is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))

  exten-short-map-cauchy-pseudocompletion-is-precomplete-short-map-Pseudometric-Space :
    is-precomplete-short-map-Pseudometric-Space P M f →
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f
  exten-short-map-cauchy-pseudocompletion-is-precomplete-short-map-Pseudometric-Space
    H =
    exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( f , H)

  iff-is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f ↔
    is-precomplete-short-map-Pseudometric-Space P M f
  pr1
    iff-is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
  pr2
    iff-is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    exten-short-map-cauchy-pseudocompletion-is-precomplete-short-map-Pseudometric-Space
```

### Extensible short maps are equivalent to precomplete short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-precomplete-extensible-short-map-Pseudometric-Space :
    extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space P M ≃
    precomplete-short-map-Pseudometric-Space P M
  equiv-precomplete-extensible-short-map-Pseudometric-Space =
    equiv-type-subtype
      ( is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( is-prop-is-precomplete-short-map-Pseudometric-Space P M)
      ( is-precomplete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( exten-short-map-cauchy-pseudocompletion-is-precomplete-short-map-Pseudometric-Space
        ( P)
        ( M))
```

### Extensible short maps are the precompositions of their extensions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
  precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space f =
    ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M f ,
      extension-precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))

  abstract
    is-section-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
      precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space ∘
      short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M) ~
      id
    is-section-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
      f =
      eq-type-subtype
        ( extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M))
        ( eq-htpy-map-short-map-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( M)
              ( f)))
          ( short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f))
          ( inv-htpy
            ( htpy-map-exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( M)
              ( f))))

    is-retraction-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
      short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M) ∘
      precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space ~
      id
    is-retraction-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
      f = refl

    is-equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
      is-equiv
        precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    is-equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
      =
      is-equiv-is-invertible
        ( short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M))
        ( is-section-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)
        ( is-retraction-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)

  equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) ≃
    extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
  equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    ( precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space ,
      is-equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

### Short maps from the Cauchy pseudocompletion of a pseudometric spaces in a metric space are the precomplete short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) ≃
    precomplete-short-map-Pseudometric-Space P M
  equiv-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    equiv-precomplete-extensible-short-map-Pseudometric-Space P M ∘e
    equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
```

### The type of extensions of a precomplete short map is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-short-map-Pseudometric-Space P M)
  where abstract

  is-contr-extension-precomplete-short-map-Pseudometric-Space :
    is-contr
      ( extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
        ( short-map-precomplete-short-map-Pseudometric-Space P M f))
  is-contr-extension-precomplete-short-map-Pseudometric-Space =
    is-proof-irrelevant-is-prop
      ( is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( short-map-precomplete-short-map-Pseudometric-Space P M f))
      ( exten-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
```
