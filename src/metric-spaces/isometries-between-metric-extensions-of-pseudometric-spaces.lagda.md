# Isometries between metric extensions of a pseudometric space

```agda
module metric-spaces.isometries-between-metric-extensions-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-extensions-of-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

An
{{#concept "isometry" Disambiguation="between metric extensions of a pseudometric space" Agda=isometry-Metric-Extension}}
between two
[metric extensions](metric-spaces.metric-extensions-of-pseudometric-spaces.md)
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P`, `i : P → M`
and `j : P → N`, is an [isometry](metric-spaces.isometries-metric-spaces.md)
`f : M → N` such that

```text
  f ∘ i ~ j.
```

## Definitions

### The property of being an isometry between metric extensions

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f :
    isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N))
  where

  coherence-triangle-prop-isometry-metric-space-Metric-Extension :
    Prop (l1 ⊔ l5)
  coherence-triangle-prop-isometry-metric-space-Metric-Extension =
    Π-Prop
      ( type-Pseudometric-Space P)
      ( λ x →
        Id-Prop
          ( set-Metric-Space
            ( metric-space-Metric-Extension P N))
          ( map-isometry-Pseudometric-Space
            ( P)
            ( pseudometric-space-Metric-Extension P N)
            ( comp-isometry-Pseudometric-Space
              ( P)
              ( pseudometric-space-Metric-Extension P M)
              ( pseudometric-space-Metric-Extension P N)
              ( f)
              ( isometry-metric-space-Metric-Extension P M))
            ( x))
          ( map-isometry-metric-space-Metric-Extension P N x))

  coherence-triangle-isometry-metric-space-Metric-Extension : UU (l1 ⊔ l5)
  coherence-triangle-isometry-metric-space-Metric-Extension =
    type-Prop
      coherence-triangle-prop-isometry-metric-space-Metric-Extension

  is-prop-coherence-triangle-isometry-metric-space-Metric-Extension :
    is-prop coherence-triangle-isometry-metric-space-Metric-Extension
  is-prop-coherence-triangle-isometry-metric-space-Metric-Extension =
    is-prop-type-Prop
      coherence-triangle-prop-isometry-metric-space-Metric-Extension
```

### The type of isometries between metric extensions of a pseudometric space

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  where

  isometry-Metric-Extension : UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  isometry-Metric-Extension =
    type-subtype
      ( coherence-triangle-prop-isometry-metric-space-Metric-Extension P M N)

module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f : isometry-Metric-Extension P M N)
  where

  isometry-metric-space-isometry-Metric-Extension :
    isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
  isometry-metric-space-isometry-Metric-Extension = pr1 f

  map-metric-space-isometry-Metric-Extension :
    type-metric-space-Metric-Extension P M →
    type-metric-space-Metric-Extension P N
  map-metric-space-isometry-Metric-Extension =
    map-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( isometry-metric-space-isometry-Metric-Extension)

  is-isometry-map-metric-space-isometry-Metric-Extension :
    is-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( map-metric-space-isometry-Metric-Extension)
  is-isometry-map-metric-space-isometry-Metric-Extension =
    is-isometry-map-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( isometry-metric-space-isometry-Metric-Extension)

  coh-isometry-Metric-Extension :
    coherence-triangle-isometry-metric-space-Metric-Extension
      ( P)
      ( M)
      ( N)
      ( isometry-metric-space-isometry-Metric-Extension)
  coh-isometry-Metric-Extension = pr2 f
```

## Properties

### The identity isometry of a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  id-isometry-Metric-Extension : isometry-Metric-Extension P M M
  pr1 id-isometry-Metric-Extension =
    isometry-id-Metric-Space
      ( metric-space-Metric-Extension P M)
  pr2 id-isometry-Metric-Extension = refl-htpy
```

### Composition of isometries between metric extensions

```agda
module _
  {l l' lu lu' lv lv' lw lw' : Level}
  (P : Pseudometric-Space l l')
  (U : Metric-Extension lu lu' P)
  (V : Metric-Extension lv lv' P)
  (W : Metric-Extension lw lw' P)
  (g : isometry-Metric-Extension P V W)
  (f : isometry-Metric-Extension P U V)
  where

  abstract
    coh-comp-isometry-Metric-Extension :
      coherence-triangle-isometry-metric-space-Metric-Extension P U W
        ( comp-isometry-Metric-Space
          ( metric-space-Metric-Extension P U)
          ( metric-space-Metric-Extension P V)
          ( metric-space-Metric-Extension P W)
          ( isometry-metric-space-isometry-Metric-Extension P V W g)
          ( isometry-metric-space-isometry-Metric-Extension P U V f))
    coh-comp-isometry-Metric-Extension x =
      ( ap
        ( map-metric-space-isometry-Metric-Extension P V W g)
        ( coh-isometry-Metric-Extension
          ( P)
          ( U)
          ( V)
          ( f)
          ( x))) ∙
      ( coh-isometry-Metric-Extension P V W g x)

  comp-isometry-Metric-Extension : isometry-Metric-Extension P U W
  pr1 comp-isometry-Metric-Extension =
    comp-isometry-Metric-Space
      ( metric-space-Metric-Extension P U)
      ( metric-space-Metric-Extension P V)
      ( metric-space-Metric-Extension P W)
      ( isometry-metric-space-isometry-Metric-Extension P V W g)
      ( isometry-metric-space-isometry-Metric-Extension P U V f)
  pr2 comp-isometry-Metric-Extension = coh-comp-isometry-Metric-Extension
```

### Homotopic isometries between metric extensions are equal

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f g : isometry-Metric-Extension P M N)
  where

  htpy-isometry-Metric-Extension : UU (l3 ⊔ l5)
  htpy-isometry-Metric-Extension =
    ( map-metric-space-isometry-Metric-Extension P M N f ~
      map-metric-space-isometry-Metric-Extension P M N g)

  is-prop-htpy-isometry-Metric-Extension :
    is-prop htpy-isometry-Metric-Extension
  is-prop-htpy-isometry-Metric-Extension =
    is-prop-Π
      ( λ x →
        is-set-type-Metric-Space
          ( metric-space-Metric-Extension P N)
          ( map-metric-space-isometry-Metric-Extension P M N f x)
          ( map-metric-space-isometry-Metric-Extension P M N g x))

  htpy-prop-isometry-Metric-Extension : Prop (l3 ⊔ l5)
  htpy-prop-isometry-Metric-Extension =
    ( htpy-isometry-Metric-Extension , is-prop-htpy-isometry-Metric-Extension)

  eq-htpy-isometry-Metric-Extension :
    htpy-isometry-Metric-Extension → f ＝ g
  eq-htpy-isometry-Metric-Extension f~g =
    eq-type-subtype
      ( coherence-triangle-prop-isometry-metric-space-Metric-Extension P M N)
      ( eq-htpy-map-isometry-Metric-Space
        ( metric-space-Metric-Extension P M)
        ( metric-space-Metric-Extension P N)
        ( isometry-metric-space-isometry-Metric-Extension P M N f)
        ( isometry-metric-space-isometry-Metric-Extension P M N g)
        ( f~g))
```
