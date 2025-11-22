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
{{#concept "isometry" Disambiguation="between metric extensions of a pseudometric space Agda=hom-isometry-Metric-Extension}}
between two
[metric extensions](metric-spaces.metric-extensions-of-pseudometric-spaces.md)
`(M , i : P → M)` and `(N , j : P → N)` of a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `P` is an
[isometry](metric-spaces.isometries-metric-spaces.md) `f : M → N` such that

```text
f ∘ i ~ j.
```

## Definitions

### The property of being an homomorphic isometry between metric extensions

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f : isometry-Metric-Space
    ( metric-space-Metric-Extension P M)
    ( metric-space-Metric-Extension P N))
  where

  is-hom-prop-isometry-metric-space-Metric-Extension : Prop (l1 ⊔ l5)
  is-hom-prop-isometry-metric-space-Metric-Extension =
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
              ( isometry-Metric-Extension P M))
            ( x))
          ( map-isometry-Metric-Extension P N x))

  is-hom-isometry-metric-space-Metric-Extension : UU (l1 ⊔ l5)
  is-hom-isometry-metric-space-Metric-Extension =
    type-Prop is-hom-prop-isometry-metric-space-Metric-Extension

  is-prop-is-hom-isometry-metric-space-Metric-Extension :
    is-prop is-hom-isometry-metric-space-Metric-Extension
  is-prop-is-hom-isometry-metric-space-Metric-Extension =
    is-prop-type-Prop is-hom-prop-isometry-metric-space-Metric-Extension
```

### The type of isometries between metric extensions of a pseudometric space

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  where

  hom-isometry-Metric-Extension : UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-isometry-Metric-Extension =
    type-subtype
      ( is-hom-prop-isometry-metric-space-Metric-Extension P M N)

module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f : hom-isometry-Metric-Extension P M N)
  where

  isometry-metric-space-hom-isometry-Metric-Extension :
    isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
  isometry-metric-space-hom-isometry-Metric-Extension = pr1 f

  map-metric-space-hom-isometry-Metric-Extension :
    type-metric-space-Metric-Extension P M →
    type-metric-space-Metric-Extension P N
  map-metric-space-hom-isometry-Metric-Extension =
    map-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( isometry-metric-space-hom-isometry-Metric-Extension)

  is-isometry-map-metric-space-hom-isometry-Metric-Extension :
    is-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( map-metric-space-hom-isometry-Metric-Extension)
  is-isometry-map-metric-space-hom-isometry-Metric-Extension =
    is-isometry-map-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P N)
      ( isometry-metric-space-hom-isometry-Metric-Extension)

  is-hom-isometry-metric-space-hom-isometry-Metric-Extension :
    ( ( map-metric-space-hom-isometry-Metric-Extension) ∘
      ( map-isometry-Metric-Extension P M)) ~
    ( map-isometry-Metric-Extension P N)
  is-hom-isometry-metric-space-hom-isometry-Metric-Extension = pr2 f
```

## Properties

### The identity isometry of a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  isometry-id-metric-space-Metric-Extension :
    isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( metric-space-Metric-Extension P M)
  isometry-id-metric-space-Metric-Extension =
    isometry-id-Metric-Space (metric-space-Metric-Extension P M)

  is-hom-isometry-id-metric-space-Metric-Extension :
    is-hom-isometry-metric-space-Metric-Extension P M M
      ( isometry-id-metric-space-Metric-Extension)
  is-hom-isometry-id-metric-space-Metric-Extension x =
    refl

  id-hom-isometry-Metric-Extension : hom-isometry-Metric-Extension P M M
  id-hom-isometry-Metric-Extension =
    ( isometry-id-metric-space-Metric-Extension ,
      is-hom-isometry-id-metric-space-Metric-Extension)
```

### Composition of isometries between metric extensions

```agda
module _
  {l l' lu lu' lv lv' lw lw' : Level}
  (P : Pseudometric-Space l l')
  (U : Metric-Extension lu lu' P)
  (V : Metric-Extension lv lv' P)
  (W : Metric-Extension lw lw' P)
  (g : hom-isometry-Metric-Extension P V W)
  (f : hom-isometry-Metric-Extension P U V)
  where

  abstract
    is-hom-comp-hom-isometry-Metric-Extension :
      is-hom-isometry-metric-space-Metric-Extension P U W
        ( comp-isometry-Metric-Space
          ( metric-space-Metric-Extension P U)
          ( metric-space-Metric-Extension P V)
          ( metric-space-Metric-Extension P W)
          ( isometry-metric-space-hom-isometry-Metric-Extension P V W g)
          ( isometry-metric-space-hom-isometry-Metric-Extension P U V f))
    is-hom-comp-hom-isometry-Metric-Extension x =
      ( ap
        ( map-metric-space-hom-isometry-Metric-Extension P V W g)
        ( is-hom-isometry-metric-space-hom-isometry-Metric-Extension
          ( P)
          ( U)
          ( V)
          ( f)
          ( x))) ∙
      ( is-hom-isometry-metric-space-hom-isometry-Metric-Extension P V W g x)

  comp-hom-isometry-Metric-Extension : hom-isometry-Metric-Extension P U W
  pr1 comp-hom-isometry-Metric-Extension =
    comp-isometry-Metric-Space
      ( metric-space-Metric-Extension P U)
      ( metric-space-Metric-Extension P V)
      ( metric-space-Metric-Extension P W)
      ( isometry-metric-space-hom-isometry-Metric-Extension P V W g)
      ( isometry-metric-space-hom-isometry-Metric-Extension P U V f)
  pr2 comp-hom-isometry-Metric-Extension =
    is-hom-comp-hom-isometry-Metric-Extension
```

### Homotopic isometries between metric extensions are equal

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( N : Metric-Extension l5 l6 P)
  ( f g : hom-isometry-Metric-Extension P M N)
  ( f~g :
    map-metric-space-hom-isometry-Metric-Extension P M N f ~
    map-metric-space-hom-isometry-Metric-Extension P M N g)
  where

  eq-htpy-map-metric-space-hom-isometry-Metric-Extension : f ＝ g
  eq-htpy-map-metric-space-hom-isometry-Metric-Extension =
    eq-type-subtype
      ( is-hom-prop-isometry-metric-space-Metric-Extension P M N)
      ( eq-htpy-map-isometry-Metric-Space
        ( metric-space-Metric-Extension P M)
        ( metric-space-Metric-Extension P N)
        ( isometry-metric-space-hom-isometry-Metric-Extension P M N f)
        ( isometry-metric-space-hom-isometry-Metric-Extension P M N g)
        ( f~g))
```
