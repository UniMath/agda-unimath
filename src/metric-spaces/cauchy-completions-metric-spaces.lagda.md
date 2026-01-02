# Cauchy completions of metric spaces

```agda
module metric-spaces.cauchy-completions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-dense-extensions-metric-spaces
open import metric-spaces.cauchy-precompletions-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.complete-extensions-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.isometries-extensions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limit-points-cauchy-precompletions-metric-spaces
open import metric-spaces.limit-points-extensions-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precomplete-extensions-metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy completion" Disambiguation="of metric space" Agda=cauchy-completion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is an
[extension](metric-spaces.extensions-metric-spaces.md) `i : M → N` of `M` that
is both [Cauchy-dense](metric-spaces.cauchy-dense-extensions-metric-spaces.md)
(i.e. all points of `N` are
[limits](metric-spaces.limit-points-extensions-metric-spaces.md) of some
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M` under the
[action](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
of `i`) and [complete](metric-spaces.complete-extensions-metric-spaces.md) (i.e.
`N` is a [complete metric space](metric-spaces.complete-metric-spaces.md)).

## Definition

### The property of being a Cauchy completion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-cauchy-completion-prop-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-completion-prop-extension-Metric-Space =
    product-Prop
      ( is-cauchy-dense-prop-extension-Metric-Space M E)
      ( is-complete-prop-extension-Metric-Space M E)

  is-cauchy-completion-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-completion-extension-Metric-Space =
    type-Prop is-cauchy-completion-prop-extension-Metric-Space

  is-prop-is-cauchy-completion-extension-Metric-Space :
    is-prop is-cauchy-completion-extension-Metric-Space
  is-prop-is-cauchy-completion-extension-Metric-Space =
    is-prop-type-Prop is-cauchy-completion-prop-extension-Metric-Space
```

### The type of Cauchy completions of a metric space

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (M : Metric-Space l1 l2)
  where

  cauchy-completion-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  cauchy-completion-Metric-Space =
    Σ ( extension-Metric-Space l3 l4 M)
      ( is-cauchy-completion-extension-Metric-Space M)

module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  extension-cauchy-completion-Metric-Space :
    extension-Metric-Space l3 l4 M
  extension-cauchy-completion-Metric-Space = pr1 C

  is-cauchy-completion-extension-cauchy-completion-Metric-Space :
    is-cauchy-completion-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space
  is-cauchy-completion-extension-cauchy-completion-Metric-Space = pr2 C

  metric-space-cauchy-completion-Metric-Space : Metric-Space l3 l4
  metric-space-cauchy-completion-Metric-Space =
    metric-space-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space

  type-metric-space-cauchy-completion-Metric-Space : UU l3
  type-metric-space-cauchy-completion-Metric-Space =
    type-metric-space-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space

  is-cauchy-dense-extension-cauchy-completion-Metric-Space :
    (y : type-metric-space-cauchy-completion-Metric-Space) →
    is-limit-point-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space)
      ( y)
  is-cauchy-dense-extension-cauchy-completion-Metric-Space =
    pr1 is-cauchy-completion-extension-cauchy-completion-Metric-Space

  is-complete-metric-space-cauchy-completion-Metric-Space :
    is-complete-Metric-Space metric-space-cauchy-completion-Metric-Space
  is-complete-metric-space-cauchy-completion-Metric-Space =
    pr2 is-cauchy-completion-extension-cauchy-completion-Metric-Space

  complete-extension-cauchy-completion-Metric-Space :
    complete-extension-Metric-Space l3 l4 M
  complete-extension-cauchy-completion-Metric-Space =
    ( extension-cauchy-completion-Metric-Space ,
      is-complete-metric-space-cauchy-completion-Metric-Space)

  precomplete-extension-cauchy-completion-Metric-Space :
    precomplete-extension-Metric-Space l3 l4 M
  precomplete-extension-cauchy-completion-Metric-Space =
    precomplete-complete-extension-Metric-Space
      ( M)
      ( complete-extension-cauchy-completion-Metric-Space)
```

## Properties

### A Cauchy completion uniquely extends the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  is-contr-isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space :
    is-contr
      ( isometry-extension-Metric-Space
        ( M)
        ( extension-cauchy-precompletion-Metric-Space M)
        ( extension-cauchy-completion-Metric-Space M C))
  is-contr-isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space
    =
    is-contr-isometry-extension-cauchy-precompletion-precomplete-extension-Metric-Space
      ( M)
      ( precomplete-extension-cauchy-completion-Metric-Space M C)

  isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space :
    isometry-extension-Metric-Space
      ( M)
      ( extension-cauchy-precompletion-Metric-Space M)
      ( extension-cauchy-completion-Metric-Space M C)
  isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space =
    center
      is-contr-isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space

  isometry-cauchy-completion-cauchy-precompletion-Metric-Space :
    isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-cauchy-completion-Metric-Space M C)
  isometry-cauchy-completion-cauchy-precompletion-Metric-Space =
    isometry-metric-space-isometry-extension-Metric-Space
      ( M)
      ( extension-cauchy-precompletion-Metric-Space M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space)

  abstract
    coh-triangle-isometry-cauchy-completion-cauchy-precompletion-Metric-Space :
      coherence-triangle-isometry-extension-Metric-Space
        ( M)
        ( extension-cauchy-precompletion-Metric-Space M)
        ( extension-cauchy-completion-Metric-Space M C)
        ( isometry-cauchy-completion-cauchy-precompletion-Metric-Space)
    coh-triangle-isometry-cauchy-completion-cauchy-precompletion-Metric-Space =
      coh-isometry-extension-Metric-Space
        ( M)
        ( extension-cauchy-precompletion-Metric-Space M)
        ( extension-cauchy-completion-Metric-Space M C)
        ( isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space)

  map-cauchy-completion-cauchy-precompletion-Metric-Space :
    type-cauchy-precompletion-Metric-Space M →
    type-metric-space-cauchy-completion-Metric-Space M C
  map-cauchy-completion-cauchy-precompletion-Metric-Space =
    map-isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( isometry-cauchy-completion-cauchy-precompletion-Metric-Space)
```

### The Cauchy precompletion extends all Cauchy completions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  isometry-extension-cauchy-precompletion-cauchy-completion-Metric-Space :
    isometry-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( extension-cauchy-precompletion-Metric-Space M)
  isometry-extension-cauchy-precompletion-cauchy-completion-Metric-Space =
    isometry-extension-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( is-cauchy-dense-extension-cauchy-completion-Metric-Space M C)

  isometry-cauchy-precompletion-cauchy-completion-Metric-Space :
    isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
  isometry-cauchy-precompletion-cauchy-completion-Metric-Space =
    isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( is-cauchy-dense-extension-cauchy-completion-Metric-Space M C)

  map-cauchy-precompletion-cauchy-completion-Metric-Space :
    type-metric-space-cauchy-completion-Metric-Space M C →
    type-cauchy-precompletion-Metric-Space M
  map-cauchy-precompletion-cauchy-completion-Metric-Space =
    map-isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-cauchy-completion-Metric-Space)

  is-isometry-map-cauchy-precompletion-cauchy-completion-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
      ( map-cauchy-precompletion-cauchy-completion-Metric-Space)
  is-isometry-map-cauchy-precompletion-cauchy-completion-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-cauchy-completion-Metric-Space)

  is-limit-map-cauchy-precompletion-cauchy-completion-Metric-Space :
    (u : type-metric-space-cauchy-completion-Metric-Space M C) →
    is-limit-cauchy-precompletion-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( u)
      ( map-cauchy-precompletion-cauchy-completion-Metric-Space u)
  is-limit-map-cauchy-precompletion-cauchy-completion-Metric-Space =
    is-limit-map-cauchy-precompletion-point-is-cauchy-dense-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( is-cauchy-dense-extension-cauchy-completion-Metric-Space M C)
```

### Any Cauchy completion is isometrically equivalent to the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where abstract

  is-section-map-cauchy-completion-cauchy-precompletion-Metric-Space :
    ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C ∘
      map-cauchy-completion-cauchy-precompletion-Metric-Space M C) ~
    ( id)
  is-section-map-cauchy-completion-cauchy-precompletion-Metric-Space =
    htpy-eq-isometry-extension-Metric-Space
      ( M)
      ( extension-cauchy-precompletion-Metric-Space M)
      ( extension-cauchy-precompletion-Metric-Space M)
      ( comp-isometry-extension-Metric-Space
        ( M)
        ( extension-cauchy-precompletion-Metric-Space M)
        ( extension-cauchy-completion-Metric-Space M C)
        ( extension-cauchy-precompletion-Metric-Space M)
        ( isometry-extension-cauchy-precompletion-cauchy-completion-Metric-Space
          ( M)
          ( C))
        ( isometry-extension-cauchy-completion-cauchy-precompletion-Metric-Space
          ( M)
          ( C)))
      ( id-isometry-extension-Metric-Space
        ( M)
        ( extension-cauchy-precompletion-Metric-Space M))
      ( eq-is-prop
        ( is-prop-isometry-extension-cauchy-precompletion-Metric-Space
          ( M)
          ( extension-cauchy-precompletion-Metric-Space M)))

  is-retraction-map-cauchy-completion-cauchy-precompletion-Metric-Space :
    ( map-cauchy-completion-cauchy-precompletion-Metric-Space M C ∘
      map-cauchy-precompletion-cauchy-completion-Metric-Space M C
      ) ~
    ( id)
  is-retraction-map-cauchy-completion-cauchy-precompletion-Metric-Space u =
    elim-exists
      ( eq-prop-Metric-Space
        ( metric-space-cauchy-completion-Metric-Space M C)
        ( map-cauchy-completion-cauchy-precompletion-Metric-Space M C
          ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C u))
        ( u))
      ( λ x x∈[u] →
        all-eq-is-limit-cauchy-approximation-Metric-Space
          ( metric-space-cauchy-completion-Metric-Space M C)
          ( map-cauchy-approximation-extension-Metric-Space
            ( M)
            ( extension-cauchy-completion-Metric-Space M C)
            ( x))
          ( map-cauchy-completion-cauchy-precompletion-Metric-Space M C
            ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C u))
          ( u)
          ( is-limit-map-cauchy-precompletion-cauchy-completion-Metric-Space
            ( M)
            ( C)
            ( map-cauchy-completion-cauchy-precompletion-Metric-Space M C
              ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C u))
            ( x ,
              inv-tr
                ( λ Z →
                  is-in-class-metric-quotient-Pseudometric-Space
                    ( cauchy-pseudocompletion-Metric-Space M)
                    ( Z)
                    ( x))
                ( is-section-map-cauchy-completion-cauchy-precompletion-Metric-Space
                  ( map-cauchy-precompletion-cauchy-completion-Metric-Space
                    ( M)
                    ( C)
                    ( u)))
                ( x∈[u])))
          ( is-limit-map-cauchy-precompletion-cauchy-completion-Metric-Space
            ( M)
            ( C)
            ( u)
            ( x , x∈[u])))
      ( is-inhabited-class-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C u))

  is-equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space :
    is-equiv
      ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C)
  is-equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space =
    is-equiv-is-invertible
      ( map-cauchy-completion-cauchy-precompletion-Metric-Space M C)
      ( is-section-map-cauchy-completion-cauchy-precompletion-Metric-Space)
      ( is-retraction-map-cauchy-completion-cauchy-precompletion-Metric-Space)
```

### The isometric equivalence between a Cauchy completion and the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space :
    type-metric-space-cauchy-completion-Metric-Space M C ≃
    type-cauchy-precompletion-Metric-Space M
  equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space =
    ( map-cauchy-precompletion-cauchy-completion-Metric-Space M C ,
      is-equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space M C)

  isometric-equiv-metric-space-cauchy-precompletion-cauchy-completion-Metric-Space :
    isometric-equiv-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
  isometric-equiv-metric-space-cauchy-precompletion-cauchy-completion-Metric-Space
    =
    ( equiv-map-cauchy-precompletion-cauchy-completion-Metric-Space ,
      is-isometry-map-cauchy-precompletion-cauchy-completion-Metric-Space M C)

module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space (l1 ⊔ l2) (l1 ⊔ l2) M)
  where

  eq-metric-space-cauchy-precompletion-cauchy-completion-Metric-Space :
    metric-space-cauchy-completion-Metric-Space M C ＝
    cauchy-precompletion-Metric-Space M
  eq-metric-space-cauchy-precompletion-cauchy-completion-Metric-Space =
    eq-isometric-equiv-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
      ( isometric-equiv-metric-space-cauchy-precompletion-cauchy-completion-Metric-Space
        ( M)
        ( C))
```
