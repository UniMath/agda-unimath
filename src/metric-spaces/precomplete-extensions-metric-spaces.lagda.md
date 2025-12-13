# Precompelte extensions of metric spaces

```agda
module metric-spaces.precomplete-extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
open import metric-spaces.action-on-cauchy-approximations-extensions-pseudometric-spaces
open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

An [extension of a metric space](metric-spaces.extensions-metric-spaces.md]
`i : M → N` is called
{{#concept "precomplete" Disambiguation="extension of metric space" Agda=is-precomplete-prop-extension-Metric-Space}}
if the
[images](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
of all
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`N`.

This is equivalent to the existence of an isometry `j : C M → N` from the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md)
of `M` into `N` such that

```text
  j ∘ κ ~ i
```

where `κ : M → C M` is the natural isometry of cauchy pseudocompletions (i.e.
the constant mapping).

## Definitions

### The property of being a precomplete extension of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-precomplete-prop-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-precomplete-prop-extension-Metric-Space =
    Π-Prop
      ( cauchy-approximation-Metric-Space M)
      ( λ u →
        is-convergent-prop-cauchy-approximation-Metric-Space
          ( metric-space-extension-Metric-Space M E)
          ( map-cauchy-approximation-extension-Metric-Space M E u))

  is-precomplete-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-precomplete-extension-Metric-Space =
    type-Prop is-precomplete-prop-extension-Metric-Space

  is-prop-is-precomplete-extension-Metric-Space :
    is-prop is-precomplete-extension-Metric-Space
  is-prop-is-precomplete-extension-Metric-Space =
    is-prop-type-Prop is-precomplete-prop-extension-Metric-Space
```

### The type of precomplete extensions of a metric space

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (M : Metric-Space l1 l2)
  where

  precomplete-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  precomplete-extension-Metric-Space =
    Σ ( extension-Metric-Space l3 l4 M)
      ( is-precomplete-extension-Metric-Space M)

module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : precomplete-extension-Metric-Space l3 l4 M)
  where

  extension-precomplete-extension-Metric-Space : extension-Metric-Space l3 l4 M
  extension-precomplete-extension-Metric-Space = pr1 E

  metric-space-precomplete-extension-Metric-Space : Metric-Space l3 l4
  metric-space-precomplete-extension-Metric-Space =
    metric-space-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  type-metric-space-precomplete-extension-Metric-Space : UU l3
  type-metric-space-precomplete-extension-Metric-Space =
    type-metric-space-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  pseudometric-space-precomplete-extension-Metric-Space :
    Pseudometric-Space l3 l4
  pseudometric-space-precomplete-extension-Metric-Space =
    pseudometric-space-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  isometry-metric-space-precomplete-extension-Metric-Space :
    isometry-Metric-Space M
      metric-space-precomplete-extension-Metric-Space
  isometry-metric-space-precomplete-extension-Metric-Space =
    isometry-metric-space-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  map-metric-space-precomplete-extension-Metric-Space :
    type-Metric-Space M →
    type-metric-space-precomplete-extension-Metric-Space
  map-metric-space-precomplete-extension-Metric-Space =
    map-metric-space-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  map-cauchy-approximation-precomplete-extension-Metric-Space :
    cauchy-approximation-Metric-Space M →
    cauchy-approximation-Metric-Space
      metric-space-precomplete-extension-Metric-Space
  map-cauchy-approximation-precomplete-extension-Metric-Space =
    map-cauchy-approximation-extension-Metric-Space M
      extension-precomplete-extension-Metric-Space

  is-precomplete-extension-precomplete-extension-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-space-precomplete-extension-Metric-Space)
      ( map-cauchy-approximation-precomplete-extension-Metric-Space u)
  is-precomplete-extension-precomplete-extension-Metric-Space = pr2 E
```

### Coherent isometries from the Cauchy pseudocompletion w.r.t. extension of metric space

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E))
  where

  coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space :
    Prop (l1 ⊔ l3)
  coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space =
    htpy-prop-isometry-Metric-Space
      ( M)
      ( metric-space-extension-Metric-Space M E)
      ( comp-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( g)
        ( isometry-cauchy-pseudocompletion-Metric-Space M))
      ( isometry-metric-space-extension-Metric-Space M E)

  coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space :
    UU (l1 ⊔ l3)
  coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space =
    type-Prop
      coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space

  is-prop-coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space :
    is-prop coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space
  is-prop-coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space =
    is-prop-type-Prop
      coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space

module _
  { l1 l2 l3 l4 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  where

  coh-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  coh-isometry-cauchy-pseudocompletion-extension-Metric-Space =
    type-subtype
      ( coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( E))
```

## Properties

### Complete metric spaces are metric spaces where the identity extension is precomplete

```agda
module _
  { l1 l2 : Level}
  ( M : Metric-Space l1 l2)
  where abstract

  eq-is-complete-is-precomplete-id-extension-Metric-Space :
    is-precomplete-extension-Metric-Space
      ( M)
      ( id-extension-Metric-Space M) ＝
    is-complete-Metric-Space M
  eq-is-complete-is-precomplete-id-extension-Metric-Space = refl
```

### The values of a coherent isometries are the limits of images of Cauchy approximations

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E))
  ( coh-g :
    coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space M E g)
  ( u : cauchy-approximation-Metric-Space M)
  where abstract

  lemma-sim-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( map-cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E)
        ( map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M)
          ( pseudometric-space-extension-Metric-Space M E)
          ( g)
          ( u)))
  lemma-sim-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space =
    inv-tr
      ( λ z →
        sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M E))
          ( z)
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M E)
            ( map-isometry-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space M)
              ( pseudometric-space-extension-Metric-Space M E)
              ( g)
              ( u))))
      ( eq-mapM-u)
      ( lemma-sim-κgu)
    where

    eq-mapM-u :
      map-cauchy-approximation-extension-Metric-Space M E u ＝
      map-cauchy-approximation-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( comp-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( pseudometric-space-extension-Metric-Space M E)
          ( g)
          ( isometry-cauchy-pseudocompletion-Metric-Space M))
        ( u)
    eq-mapM-u =
      htpy-map-cauchy-approximation-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( isometry-metric-space-extension-Metric-Space M E)
        ( comp-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( pseudometric-space-extension-Metric-Space M E)
          ( g)
          ( isometry-cauchy-pseudocompletion-Metric-Space M))
        ( inv-htpy coh-g)
        ( u)

    lemma-sim-κgu :
      sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M E))
        ( map-cauchy-approximation-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( pseudometric-space-extension-Metric-Space M E)
          ( comp-isometry-Pseudometric-Space
            ( pseudometric-Metric-Space M)
            ( cauchy-pseudocompletion-Metric-Space M)
            ( pseudometric-space-extension-Metric-Space M E)
            ( g)
            ( isometry-cauchy-pseudocompletion-Metric-Space M))
            ( u))
        ( map-cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M E)
          ( map-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( pseudometric-space-extension-Metric-Space M E)
            ( g)
            ( u)))
    lemma-sim-κgu =
      tr
        (
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-extension-Metric-Space M E))
            ( map-cauchy-approximation-isometry-Pseudometric-Space
              ( pseudometric-Metric-Space M)
              ( pseudometric-space-extension-Metric-Space M E)
              ( comp-isometry-Pseudometric-Space
                ( pseudometric-Metric-Space M)
                ( cauchy-pseudocompletion-Metric-Space M)
                ( pseudometric-space-extension-Metric-Space M E)
                ( g)
                ( isometry-cauchy-pseudocompletion-Metric-Space M))
              ( u)))
        ( htpy-map-cauchy-approximation-extension-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M)
          ( pseudometric-space-extension-Metric-Space M E , g)
          ( u))
        ( preserves-sim-map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M))
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-extension-Metric-Space M E))
          ( isometry-map-cauchy-approximation-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( pseudometric-space-extension-Metric-Space M E)
            ( g))
          ( map-cauchy-approximation-isometry-Pseudometric-Space
            ( pseudometric-Metric-Space M)
            ( cauchy-pseudocompletion-Metric-Space M)
            ( isometry-cauchy-pseudocompletion-Metric-Space M)
            ( u))
          ( map-cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( u))
          ( sim-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( pseudometric-Metric-Space M)
            ( u)))

  is-limit-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-extension-Metric-Space M E)
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( g)
        ( u))
  is-limit-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space =
    is-limit-sim-const-cauchy-approximation-Metric-Space
      ( metric-space-extension-Metric-Space M E)
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( g)
        ( u))
      ( lemma-sim-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space)
```

### An extension with a coherent isometry from the Cauchy pseudocompletion is precomplete

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E))
  ( coh-g :
    coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space M E g)
  where abstract

  is-precomplete-has-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    is-precomplete-extension-Metric-Space M E
  is-precomplete-has-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
    u =
    ( ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( g)
        ( u)) ,
      ( is-limit-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( E)
        ( g)
        ( coh-g)
        ( u)))
```

### All coherent isometries from the cauchy pseudocompletion are homotopic

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  ( g h :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E))
  ( coh-g :
    coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space M E g)
  ( coh-h :
    coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space M E h)
  where abstract

  all-htpy-is-coh-isometry-cauchjy-pseudocompletion-extension-Metric-Space :
    htpy-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E)
      ( g)
      ( h)
  all-htpy-is-coh-isometry-cauchjy-pseudocompletion-extension-Metric-Space u =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( metric-space-extension-Metric-Space M E)
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( g)
        ( u))
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( h)
        ( u))
      ( is-limit-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( E)
        ( g)
        ( coh-g)
        ( u))
      ( is-limit-coherent-isometry-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( E)
        ( h)
        ( coh-h)
        ( u))
```

### All coherent isometries from the cauchy pseudocompletion are equal

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where abstract

  all-eq-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    ( g h : coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E) →
    ( g ＝ h)
  all-eq-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
    (g , coh-g) (h , coh-h) =
    eq-type-subtype
      ( coherence-triangle-prop-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( E))
      ( eq-htpy-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-extension-Metric-Space M E)
        ( all-htpy-is-coh-isometry-cauchjy-pseudocompletion-extension-Metric-Space
          ( M)
          ( E)
          ( g)
          ( h)
          ( coh-g)
          ( coh-h)))
```

### The type of coherent isometries from the Cauchy pseudocompletion w.r.t an extension of metric space is a proposition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where abstract

  is-prop-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space :
    is-prop
      ( coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E)
  is-prop-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space =
    is-prop-all-elements-equal
      ( all-eq-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E)

  coh-isometry-cauchy-pseudocompletion-prop-extension-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  coh-isometry-cauchy-pseudocompletion-prop-extension-Metric-Space =
    ( coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E ,
      is-prop-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space)
```

### A precomplete extension induces a coherent isometry from the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : precomplete-extension-Metric-Space l3 l4 M)
  where

  map-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
    cauchy-approximation-Metric-Space M →
    type-metric-space-precomplete-extension-Metric-Space M E
  map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u =
    limit-is-convergent-cauchy-approximation-Metric-Space
      ( metric-space-precomplete-extension-Metric-Space M E)
      ( map-cauchy-approximation-precomplete-extension-Metric-Space M E u)
      ( is-precomplete-extension-precomplete-extension-Metric-Space M E u)

  abstract
    sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
      (u : cauchy-approximation-Metric-Space M) →
      sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E))
        ( map-cauchy-approximation-precomplete-extension-Metric-Space M E u)
        ( map-cauchy-pseudocompletion-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E)
          ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u))
    sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u =
      sim-const-is-limit-cauchy-approximation-Metric-Space
        ( metric-space-precomplete-extension-Metric-Space M E)
        ( map-cauchy-approximation-precomplete-extension-Metric-Space M E u)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)
        ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E)
          ( map-cauchy-approximation-precomplete-extension-Metric-Space M E u)
          ( is-precomplete-extension-precomplete-extension-Metric-Space M E u))

    preserves-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
      is-short-function-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-precomplete-extension-Metric-Space M E)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space)
    preserves-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
      d u v Nuv =
      reflects-neighborhoods-map-isometry-Pseudometric-Space
        ( pseudometric-space-precomplete-extension-Metric-Space M E)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E))
        ( isometry-cauchy-pseudocompletion-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E))
        ( d)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space v)
        ( preserves-neighborhoods-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E))
          { map-cauchy-approximation-precomplete-extension-Metric-Space M E u}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)}
          { map-cauchy-approximation-precomplete-extension-Metric-Space M E v}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space v)}
          ( sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
            ( u))
          ( sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
            ( v))
          ( d)
          ( preserves-neighborhoods-map-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M)
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-precomplete-extension-Metric-Space M E))
            ( isometry-cauchy-pseudocompletion-extension-Metric-Space M
              ( extension-precomplete-extension-Metric-Space M E))
            ( d)
            ( u)
            ( v)
            ( Nuv)))

    reflects-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
      (d : ℚ⁺) →
      (u v : cauchy-approximation-Metric-Space M) →
      neighborhood-Metric-Space
        ( metric-space-precomplete-extension-Metric-Space M E)
        ( d)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space v) →
      neighborhood-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( d)
        ( u)
        ( v)
    reflects-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
      d u v Nxy =
      reflects-neighborhoods-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E))
        ( isometry-cauchy-pseudocompletion-extension-Metric-Space M
          ( extension-precomplete-extension-Metric-Space M E))
        ( d)
        ( u)
        ( v)
        ( reflects-neighborhoods-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E))
          { map-cauchy-approximation-precomplete-extension-Metric-Space M E u}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)}
          { map-cauchy-approximation-precomplete-extension-Metric-Space M E v}
          { map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-precomplete-extension-Metric-Space M E)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space v)}
          ( sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
            ( u))
          ( sim-const-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
            ( v))
          ( d)
          ( preserves-neighborhoods-map-isometry-Pseudometric-Space
            ( pseudometric-space-precomplete-extension-Metric-Space M E)
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-precomplete-extension-Metric-Space M E))
            ( isometry-cauchy-pseudocompletion-Metric-Space
              ( metric-space-precomplete-extension-Metric-Space M E))
            ( d)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space u)
            ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space v)
            ( Nxy)))

    is-isometry-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
      is-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-space-precomplete-extension-Metric-Space M E)
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space)
    is-isometry-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
      d u v =
      ( ( preserves-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
          d
          u
          v) ,
        ( reflects-neighborhoods-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
          d
          u
          v))

  isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-space-precomplete-extension-Metric-Space M E)
  isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space =
    ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space ,
      is-isometry-map-cauchy-pseudocompletion-precomplete-extension-Metric-Space)

  abstract
    coherence-triangle-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
      coherence-triangle-cauchy-pseudocompletion-extension-Metric-Space
        ( M)
        ( extension-precomplete-extension-Metric-Space M E)
        ( isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space)
    coherence-triangle-cauchy-pseudocompletion-precomplete-extension-Metric-Space
      x =
      all-eq-is-limit-cauchy-approximation-Metric-Space
        ( metric-space-precomplete-extension-Metric-Space M E)
        ( map-cauchy-approximation-precomplete-extension-Metric-Space M E
          ( map-cauchy-pseudocompletion-Metric-Space M x))
        ( map-cauchy-pseudocompletion-precomplete-extension-Metric-Space
          ( map-cauchy-pseudocompletion-Metric-Space M x))
        ( map-metric-space-precomplete-extension-Metric-Space M E x)
        ( is-limit-limit-convergent-cauchy-approximation-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E)
          ( ( map-cauchy-approximation-extension-Metric-Space M
              ( extension-precomplete-extension-Metric-Space M E)
              ( map-cauchy-pseudocompletion-Metric-Space M x)) ,
            is-precomplete-extension-precomplete-extension-Metric-Space M E
              (map-cauchy-pseudocompletion-Metric-Space M x)))
        ( is-limit-const-cauchy-approximation-Metric-Space
          ( metric-space-precomplete-extension-Metric-Space M E)
          ( map-metric-space-precomplete-extension-Metric-Space M E x))

  coh-isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space :
    coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
      ( M)
      ( extension-precomplete-extension-Metric-Space M E)
  coh-isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space =
    ( isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space ,
      coherence-triangle-cauchy-pseudocompletion-precomplete-extension-Metric-Space)
```

### An extension of metric space is precomplete if and only if it admits a coherent isometry from the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where abstract

  iff-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space :
    is-precomplete-extension-Metric-Space M E ↔
    coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E
  pr1
    iff-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space
    H =
    coh-isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space
      ( M)
      ( E , H)
  pr2
    iff-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space
    (g , coh-g) =
    is-precomplete-has-coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
      ( M)
      ( E)
      ( g)
      ( coh-g)

  equiv-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space :
    is-precomplete-extension-Metric-Space M E ≃
    coh-isometry-cauchy-pseudocompletion-extension-Metric-Space M E
  equiv-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space
    =
    equiv-iff'
      ( is-precomplete-prop-extension-Metric-Space M E)
      ( coh-isometry-cauchy-pseudocompletion-prop-extension-Metric-Space M E)
      ( iff-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space)
```

### A metric space is complete if and only if it admits a coherent isometry from its Cauchy pseudocompletion into itself

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  equiv-coh-isometry-cauchy-pseudocompletion-is-complete-Metric-Space :
    is-complete-Metric-Space M ≃
    coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
      ( M)
      ( id-extension-Metric-Space M)
  equiv-coh-isometry-cauchy-pseudocompletion-is-complete-Metric-Space =
    tr
      ( λ X →
        X ≃
        coh-isometry-cauchy-pseudocompletion-extension-Metric-Space
          ( M)
          ( id-extension-Metric-Space M))
      ( eq-is-complete-is-precomplete-id-extension-Metric-Space M)
      ( equiv-coh-isometry-cauchy-pseudocompletion-is-precomplete-extension-Metric-Space
        ( M)
        ( id-extension-Metric-Space M))
```
