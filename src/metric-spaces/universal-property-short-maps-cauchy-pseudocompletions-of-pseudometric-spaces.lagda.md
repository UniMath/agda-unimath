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
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
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

maps [short maps](metric-spaces.short-maps-pseudometric-spaces.md) `g : C P → M`
short maps `g ∘ κ : P → M`. For any
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md),
`u : C P`, its
[image](metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces.md)
`C(g ∘ κ) u : C M`
[converges](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) to
`g u` so `g` is determined by its restriction to `P`.

Conversely, a short map `f : P → M`, extends along `κ`, i.e. there exists a
short map `g : C P → M` such that

```text
  g ∘ κ ~ f
```

if and only if the images `Cf u` of Cauchy approximations `u : C P` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`M`. In that case, `f` is called a
{{#concept "complete short map" Disambiguation="from a pseudometric space to a metric space" Agda=complete-short-map-Pseudometric-Space}}
from `P` to `M`. The type of short maps for the Cauchy pseudocompletion `C P` of
a pseudometric space `P` to a metric space `M` is equivalent to the type of
**complete short maps** from `P` to `M`.

Equivalently, the Cauchy pseudocompletion satisfies satisfies the
{{#concept "universal property" Disambiguation="of Cauchy pseudocompletions and complete short maps" Agda=is-contr-extension-complete-short-map-Pseudometric-Space}}
of Cauchy precompletions and complete short maps: for any complete short map
`f : P → M` from a pseudometric space in a metric space, there
[uniquely exists](foundation.uniqueness-quantification.md) an extension of `f`
along `κ`.

## Definitions

### Precomposition of short maps by the natural inclusion of pseudometric spaces into their Cauchy pseudocompletions

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

### Extensions of short maps along the natural isometry of Cauchy pseudocompletions

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

  is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    Π-Prop
      ( type-Pseudometric-Space P)
      ( λ x →
        eq-prop-Metric-Space
          ( M)
          ( map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( M)
              ( g))
            ( x))
          ( map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)
            ( x)))

  is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    UU (l1 ⊔ l1')
  is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    type-Prop
      is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space

  is-prop-is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-prop
      is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
  is-prop-is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    is-prop-type-Prop
      is-extension-prop-short-map-cauchy-pseudocompletion-Pseudometric-Space

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
    map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space ∘
    map-unit-cauchy-pseudocompletion-Pseudometric-Space P ~
    map-short-map-Pseudometric-Space P (pseudometric-Metric-Space M) f
  htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    pr2 g
```

### Extensible short maps

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
    htpy-map-short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
      ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M
        short-map-exten-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)
      ( short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  htpy-map-exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    pr2
      exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
```

### The property of being a complete short map from a pseudometric space in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-complete-prop-short-map-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-complete-prop-short-map-Pseudometric-Space =
    Π-Prop
      ( cauchy-approximation-Pseudometric-Space P)
      ( is-convergent-prop-cauchy-approximation-Metric-Space M ∘
        map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( f))

  is-complete-short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  is-complete-short-map-Pseudometric-Space =
    type-Prop is-complete-prop-short-map-Pseudometric-Space

  is-prop-is-complete-short-map-Pseudometric-Space :
    is-prop is-complete-short-map-Pseudometric-Space
  is-prop-is-complete-short-map-Pseudometric-Space =
    is-prop-type-Prop is-complete-prop-short-map-Pseudometric-Space
```

### The type of complete short maps from a pseudometric space to a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  complete-short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  complete-short-map-Pseudometric-Space =
    type-subtype
      ( is-complete-prop-short-map-Pseudometric-Space P M)

  short-map-complete-short-map-Pseudometric-Space :
    complete-short-map-Pseudometric-Space →
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  short-map-complete-short-map-Pseudometric-Space = pr1

  map-complete-short-map-Pseudometric-Space :
    complete-short-map-Pseudometric-Space →
    map-Pseudometric-Space P (pseudometric-Metric-Space M)
  map-complete-short-map-Pseudometric-Space f =
    map-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( short-map-complete-short-map-Pseudometric-Space f)

  is-complete-short-map-complete-short-map-Pseudometric-Space :
    (f : complete-short-map-Pseudometric-Space) →
    is-complete-short-map-Pseudometric-Space P M
      ( short-map-complete-short-map-Pseudometric-Space f)
  is-complete-short-map-complete-short-map-Pseudometric-Space = pr2
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

### A complete short map extends to the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : complete-short-map-Pseudometric-Space P M)
  where

  map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space u =
    limit-is-convergent-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-complete-short-map-Pseudometric-Space P M f)
        ( u))
      ( is-complete-short-map-complete-short-map-Pseudometric-Space P M f u)

  sim-const-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    (u : cauchy-approximation-Pseudometric-Space P) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-complete-short-map-Pseudometric-Space P M f)
        ( u))
      ( map-unit-cauchy-pseudocompletion-Metric-Space M
        ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( u)))
  sim-const-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-complete-short-map-Pseudometric-Space P M f)
        ( u))
      ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space u)
      ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
        ( M)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-complete-short-map-Pseudometric-Space P M f)
          ( u))
        ( is-complete-short-map-complete-short-map-Pseudometric-Space P M f u))

  is-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  is-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    d u v Nuv =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-unit-cauchy-pseudocompletion-Metric-Space M)
      ( d)
      ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space u)
      ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space v)
      ( preserves-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        { map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-complete-short-map-Pseudometric-Space P M f)
          ( u)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( u))}
        { map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-complete-short-map-Pseudometric-Space P M f)
          ( v)}
        { map-unit-cauchy-pseudocompletion-Metric-Space M
          ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( v))}
        ( sim-const-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( u))
        ( sim-const-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( v))
        ( d)
        ( is-short-map-short-map-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( short-map-complete-short-map-Pseudometric-Space P M f))
          ( d)
          ( u)
          ( v)
          ( Nuv)))

  short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
  short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space ,
      is-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space)

  is-extension-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    is-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( short-map-complete-short-map-Pseudometric-Space P M f)
      ( short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
  is-extension-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
    x =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( short-map-complete-short-map-Pseudometric-Space P M f)
        ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
      ( map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
      ( map-complete-short-map-Pseudometric-Space P M f x)
      ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
        ( M)
        ( map-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( short-map-complete-short-map-Pseudometric-Space P M f)
          ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x))
        ( is-complete-short-map-complete-short-map-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( map-unit-cauchy-pseudocompletion-Pseudometric-Space P x)))
      ( is-limit-const-cauchy-approximation-Metric-Space M
        ( map-complete-short-map-Pseudometric-Space P M f x))

  exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
      ( short-map-complete-short-map-Pseudometric-Space P M f)
  exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    ( short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space ,
      is-extension-short-map-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space)
```

### The values of extensions of short maps are limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f)
  where

  htpy-map-precomp-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    htpy-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( precomp-short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)))
      ( short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))
  htpy-map-precomp-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    htpy-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( precomp-short-map-unit-cauchy-pseudocompletion-Pseudometric-Space P M
        ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)))
      ( f)
      ( htpy-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))

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
    binary-tr
      ( sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M))
      ( htpy-map-precomp-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g)
        ( u))
      ( coh-square-map-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-Metric-Space M)
        ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g))
        ( u))
      ( preserves-sim-map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( cauchy-pseudocompletion-Metric-Space M)
        ( short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-Metric-Space M)
          ( short-map-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f)
            ( g)))
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

### All extensions of short maps to the Cauchy pseudocompletion are homotopic

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

### A short map extends to the Cauchy pseudocompletion if and only if it is complete

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f →
    is-complete-short-map-Pseudometric-Space P M f
  is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
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

  iff-is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space :
    extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M f ↔
    is-complete-short-map-Pseudometric-Space P M f
  pr1
    iff-is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
  pr2
    iff-is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
    =
    exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space P M ∘
    pair f
```

### Extensible short maps are equivalent to complete short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-complete-extensible-short-map-Pseudometric-Space :
    extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space P M ≃
    complete-short-map-Pseudometric-Space P M
  equiv-complete-extensible-short-map-Pseudometric-Space =
    equiv-type-subtype
      ( is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( is-prop-is-complete-short-map-Pseudometric-Space P M)
      ( is-complete-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M))
      ( λ f H →
        exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
          ( f , H))
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
          ( htpy-map-exten-short-map-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( M)
            ( f)))

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

### Short maps from the Cauchy pseudocompletion of a pseudometric spaces in a metric space are the complete short maps

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
    complete-short-map-Pseudometric-Space P M
  equiv-short-map-cauchy-pseudocompletion-Pseudometric-Space =
    equiv-complete-extensible-short-map-Pseudometric-Space P M ∘e
    equiv-precomp-extensible-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( P)
      ( M)
```

### The type of extensions of a complete short map is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : complete-short-map-Pseudometric-Space P M)
  where abstract

  is-contr-extension-complete-short-map-Pseudometric-Space :
    is-contr
      ( extension-short-map-cauchy-pseudocompletion-Pseudometric-Space P M
        ( short-map-complete-short-map-Pseudometric-Space P M f))
  is-contr-extension-complete-short-map-Pseudometric-Space =
    is-proof-irrelevant-is-prop
      ( is-prop-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( short-map-complete-short-map-Pseudometric-Space P M f))
      ( exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( M)
        ( f))
```
