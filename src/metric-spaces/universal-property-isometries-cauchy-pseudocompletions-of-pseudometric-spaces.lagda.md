# Universal property of Cauchy pseudocompletions of pseudometric spaces and isometries into metric spaces

```agda
module metric-spaces.universal-property-isometries-cauchy-pseudocompletions-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

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
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.universal-property-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
```

</details>

## Idea

Given a [metric space](metric-spaces.metric-spaces.md) `M` and a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `P`, precomposition
with the unit [isometry](metric-spaces.isometries-pseudometric-spaces.md) of
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md)

```text
  κ : P → C P
```

maps isometries `g : C P → M` to isometries `g ∘ κ : P → M`. For any
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md),
`u : C P`, its
[image](metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces.md)
`C(g ∘ κ) u : C M`
[converges](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) to
`g u` so `g` is determined by its restriction to `P`.

Conversely, an isometry `f : P → M`, extends along `κ`, i.e. there exists a
isometry `g : C P → M` such that

```text
  g ∘ κ ~ f
```

if and only if the images `Cf u` of Cauchy approximations `u : C P` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`M`. In that case, `f` is called a
{{#concept "precomplete isometry" Disambiguation="from a pseudometric space to a metric space" Agda=precomplete-isometry-Pseudometric-Space}}
from `P` to `M`. The type of isometries from the Cauchy pseudocompletion `C P`
of a pseudometric space `P` to a metric space `M` is equivalent to the type of
**precomplete isometries** from `P` to `M`.

Equivalently, the Cauchy pseudocompletion satisfies satisfies the
{{#concept "universal property" Disambiguation="of Cauchy pseudocompletions and precomplete isometries" Agda=is-contr-extension-precomplete-isometry-Pseudometric-Space}}
of Cauchy precompletions and precomplete isometries: for any precomplete
isometry `f : P → M` from a pseudometric space in a metric space, there
[uniquely exists](foundation.uniqueness-quantification.md) an extension of `f`
along `κ`.

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

### Extensions of isometries along the unit map of Cauchy pseudocompletions

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Space l1' l2')
  ( f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M))
  where

  is-extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  is-extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
      ( short-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( g))

  is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l1')
  is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    type-Prop
      is-extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space

  is-prop-is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-prop
      is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
  is-prop-is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    is-prop-type-Prop
      is-extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    Σ ( isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M))
      ( is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f)
  where

  isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    pr1 g

  precomp-isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space ∘
    map-unit-cauchy-pseudocompletion-Pseudometric-Space P ~
    map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f
  htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    pr2 g

  extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
  pr1 extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    short-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  pr2 extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
```

### Extensible isometries along the unit map of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    Σ ( isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
      ( extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space P M)
  where

  isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    = pr1 f

  exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
      isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
  exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    = pr2 f

  isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    pr1
      exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space

  htpy-map-exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    htpy-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
      ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M
        isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space)
      ( isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  htpy-map-exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    pr2
      exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
```

### The property of being a precomplete isometry from a pseudometric space to a metric space

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

### The precomplete short map induced by a precomplete isometry

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

## Properties

### An isometry from the Cauchy pseudocompletion extends its precomposition by the unit map

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

  extension-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space :
    extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
      ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M g)
  extension-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space =
    ( g , refl-htpy)
```

### A precomplete isometry extends to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-isometry-Pseudometric-Space P M)
  where

  short-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  short-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    short-map-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( precomplete-short-map-precomplete-isometry-Pseudometric-Space P M f)

  map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( short-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  sim-const-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    (u : cauchy-approximation-Pseudometric-Space P) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( u)))
  sim-const-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    sim-const-map-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( precomplete-short-map-precomplete-isometry-Pseudometric-Space P M f)

  preserves-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  preserves-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-short-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( short-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  reflects-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    (d : ℚ⁺) →
    (u v : cauchy-approximation-Pseudometric-Space P) →
    neighborhood-Metric-Space M d
      ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space u)
      ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space v) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( d)
      ( u)
      ( v)
  reflects-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    d u v Nuv =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
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
          ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( u))}
        { map-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( isometry-precomplete-isometry-Pseudometric-Space P M f)
          ( v)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( v))}
        ( sim-const-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( u))
        ( sim-const-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( v))
        ( d)
        ( preserves-neighborhoods-map-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( isometry-unit-cauchy-pseudocompletion-Metric-Space M)
          ( d)
          ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( u))
          ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( v))
          ( Nuv)))

  is-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    d u v =
    ( ( preserves-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( d)
        ( u)
        ( v)) ,
      ( reflects-neighborhoods-map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( d)
        ( u)
        ( v)))

  isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space ,
      is-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  is-extension-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
      ( isometry-precomplete-isometry-Pseudometric-Space P M f)
      ( isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
  is-extension-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-extension-short-map-precomplete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( precomplete-short-map-precomplete-isometry-Pseudometric-Space P M f)

  exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
      ( isometry-precomplete-isometry-Pseudometric-Space P M f)
  exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    ( isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space ,
      is-extension-isometry-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space)
```

### The values of extensions of isometries are limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f)
  where

  htpy-map-precomp-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    htpy-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)))
      ( isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
  htpy-map-precomp-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    htpy-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M
        ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)))
      ( f)
      ( htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f)
  (u : cauchy-approximation-Pseudometric-Space P)
  where abstract

  sim-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)
          ( u)))
  sim-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    sim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
      ( extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))
      ( u)

  is-lim-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f)
        ( u))
      ( map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
  is-lim-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    is-lim-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
      ( extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))
      ( u)
```

### All extensions of a isometry to the Cauchy pseudocompletion are homotopic

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  all-htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    ( g h :
      extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f) →
    map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f g ~
    map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f h
  all-htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    g h =
    all-htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
      ( extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))
      ( extension-short-map-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( h))
```

### Extensions of isometries are unique

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  all-eq-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    ( g h :
      extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f) →
    ( g ＝ h)
  all-eq-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space g h =
    eq-type-subtype
      ( is-extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
      ( eq-htpy-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( isometry-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( h))
        ( all-htpy-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)
          ( h)))

  is-prop-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    is-prop
      ( extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f)
  is-prop-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    is-prop-all-elements-equal
      all-eq-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
```

### The property of being an isometry extensible to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    ( extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f ,
      is-prop-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
```

### An isometry extends to the Cauchy pseudocompletion if and only if it is precomplete

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f →
    is-precomplete-isometry-Pseudometric-Space P M f
  is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    g u =
    ( map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u) ,
      is-lim-map-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))

  iff-is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M f ↔
    is-precomplete-isometry-Pseudometric-Space P M f
  pr1
    iff-is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
  pr2
    iff-is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space P M ∘
    pair f
```

### Extensible isometries are equivalent to precomplete isometries

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-precomplete-extensible-isometry-Pseudometric-Space :
    extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space P M ≃
    precomplete-isometry-Pseudometric-Space P M
  equiv-precomplete-extensible-isometry-Pseudometric-Space =
    equiv-type-subtype
      ( is-prop-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( is-prop-is-precomplete-isometry-Pseudometric-Space P M)
      ( is-precomplete-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( λ f H →
        exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f , H))
```

### Extensible isometries are the precompositions of their extensions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) →
    extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
  precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space f =
    ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space P M f ,
      extension-precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))

  abstract
    is-section-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
      precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space ∘
      isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M) ~
      id
    is-section-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
      f =
      eq-type-subtype
        ( extension-prop-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M))
        ( eq-htpy-map-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( M)
              ( f)))
          ( isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f))
          ( htpy-map-exten-isometry-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f)))

    is-retraction-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
      isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M) ∘
      precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space ~
      id
    is-retraction-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
      f = refl

    is-equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
      is-equiv
        precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    is-equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
      =
      is-equiv-is-invertible
        ( isometry-exten-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M))
        ( is-section-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space)
        ( is-retraction-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space)

  equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) ≃
    extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
  equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
    =
    ( precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space ,
      is-equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space)
```

### Isometries from the Cauchy pseudocompletion of a pseudometric spaces in a metric space are the precomplete isometries

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-isometry-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M) ≃
    precomplete-isometry-Pseudometric-Space P M
  equiv-isometry-cauchy-pseudocompletion-Pseudometric-Space =
    equiv-precomplete-extensible-isometry-Pseudometric-Space P M ∘e
    equiv-precomp-extensible-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
```

### The type of extensions of a precomplete isometry is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : precomplete-isometry-Pseudometric-Space P M)
  where abstract

  is-contr-extension-precomplete-isometry-Pseudometric-Space :
    is-contr
      ( extension-isometry-cauchy-pseudocompletion-Pseudometric-Space P M
        ( isometry-precomplete-isometry-Pseudometric-Space P M f))
  is-contr-extension-precomplete-isometry-Pseudometric-Space =
    is-proof-irrelevant-is-prop
      ( is-prop-extension-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( isometry-precomplete-isometry-Pseudometric-Space P M f))
      ( exten-precomplete-isometry-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
```
