# Isometries between metric extensions of a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.isometries-extensions-metric-spaces where
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
open import foundation.whiskering-homotopies-composition

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
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
{{#concept "isometry" Disambiguation="between extensions of a metric space" Agda=isometry-extension-Metric-Space}}
between two [extensions](metric-spaces.extensions-metric-spaces.md) of a
[metric space](metric-spaces.metric-spaces.md) `M`, `i : M → U` and `j : M → V`,
is an [isometry](metric-spaces.isometries-metric-spaces.md) `f : U → V` such
that

```text
  f ∘ i ~ j.
```

## Definitions

### Coherence triangle of extensions of a metric space

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( M : Metric-Space l1 l2)
  ( U : extension-Metric-Space l3 l4 M)
  ( V : extension-Metric-Space l5 l6 M)
  ( f :
    isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V))
  where

  coherence-triangle-prop-isometry-extension-Metric-Space : Prop (l1 ⊔ l5)
  coherence-triangle-prop-isometry-extension-Metric-Space =
    Π-Prop
      ( type-Metric-Space M)
      ( λ x →
        eq-prop-Metric-Space
          ( metric-space-extension-Metric-Space M V)
          ( map-isometry-Metric-Space
            ( M)
            ( metric-space-extension-Metric-Space M V)
            ( comp-isometry-Metric-Space
              ( M)
              ( metric-space-extension-Metric-Space M U)
              ( metric-space-extension-Metric-Space M V)
              ( f)
              ( isometry-metric-space-extension-Metric-Space M U))
            ( x))
          ( map-metric-space-extension-Metric-Space M V x))

  coherence-triangle-isometry-extension-Metric-Space : UU (l1 ⊔ l5)
  coherence-triangle-isometry-extension-Metric-Space =
    type-Prop
      coherence-triangle-prop-isometry-extension-Metric-Space

  is-prop-coherence-triangle-isometry-extension-Metric-Space :
    is-prop coherence-triangle-isometry-extension-Metric-Space
  is-prop-coherence-triangle-isometry-extension-Metric-Space =
    is-prop-type-Prop
      coherence-triangle-prop-isometry-extension-Metric-Space
```

### The type of isometries between extensions of a metric space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (V : extension-Metric-Space l5 l6 M)
  where

  isometry-extension-Metric-Space : UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  isometry-extension-Metric-Space =
    type-subtype
      ( coherence-triangle-prop-isometry-extension-Metric-Space M U V)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (V : extension-Metric-Space l5 l6 M)
  (f : isometry-extension-Metric-Space M U V)
  where

  isometry-metric-space-isometry-extension-Metric-Space :
    isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V)
  isometry-metric-space-isometry-extension-Metric-Space = pr1 f

  map-metric-space-isometry-extension-Metric-Space :
    type-metric-space-extension-Metric-Space M U →
    type-metric-space-extension-Metric-Space M V
  map-metric-space-isometry-extension-Metric-Space =
    map-isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V)
      ( isometry-metric-space-isometry-extension-Metric-Space)

  is-isometry-map-metric-space-isometry-extension-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V)
      ( map-metric-space-isometry-extension-Metric-Space)
  is-isometry-map-metric-space-isometry-extension-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V)
      ( isometry-metric-space-isometry-extension-Metric-Space)

  coh-isometry-extension-Metric-Space :
    coherence-triangle-isometry-extension-Metric-Space M U V
      ( isometry-metric-space-isometry-extension-Metric-Space)
  coh-isometry-extension-Metric-Space = pr2 f
```

## Properties

### Isometries of metric spaces are isometries of extensions of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (N : Metric-Space l3 l4)
  (f : isometry-Metric-Space M N)
  where

  isometry-extension-isometry-Metric-Space :
    isometry-extension-Metric-Space
      ( M)
      ( id-extension-Metric-Space M)
      ( extension-isometry-Metric-Space M N f)
  isometry-extension-isometry-Metric-Space = (f , refl-htpy)
```

### The identity isometry

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  where

  id-isometry-extension-Metric-Space : isometry-extension-Metric-Space M U U
  pr1 id-isometry-extension-Metric-Space =
    id-isometry-Metric-Space (metric-space-extension-Metric-Space M U)
  pr2 id-isometry-extension-Metric-Space = refl-htpy
```

### Composition of isometries between extensions of a metric space

```agda
module _
  {l l' lu lu' lv lv' lw lw' : Level}
  (M : Metric-Space l l')
  (U : extension-Metric-Space lu lu' M)
  (V : extension-Metric-Space lv lv' M)
  (W : extension-Metric-Space lw lw' M)
  (g : isometry-extension-Metric-Space M V W)
  (f : isometry-extension-Metric-Space M U V)
  where

  abstract
    coh-comp-isometry-extension-Metric-Space :
      coherence-triangle-isometry-extension-Metric-Space M U W
        ( comp-isometry-Metric-Space
          ( metric-space-extension-Metric-Space M U)
          ( metric-space-extension-Metric-Space M V)
          ( metric-space-extension-Metric-Space M W)
          ( isometry-metric-space-isometry-extension-Metric-Space M V W g)
          ( isometry-metric-space-isometry-extension-Metric-Space M U V f))
    coh-comp-isometry-extension-Metric-Space =
      ( ( map-metric-space-isometry-extension-Metric-Space M V W g) ·l
        ( coh-isometry-extension-Metric-Space M U V f)) ∙h
      ( coh-isometry-extension-Metric-Space M V W g)

  comp-isometry-extension-Metric-Space : isometry-extension-Metric-Space M U W
  pr1 comp-isometry-extension-Metric-Space =
    comp-isometry-Metric-Space
      ( metric-space-extension-Metric-Space M U)
      ( metric-space-extension-Metric-Space M V)
      ( metric-space-extension-Metric-Space M W)
      ( isometry-metric-space-isometry-extension-Metric-Space M V W g)
      ( isometry-metric-space-isometry-extension-Metric-Space M U V f)
  pr2 comp-isometry-extension-Metric-Space =
    coh-comp-isometry-extension-Metric-Space
```

### Homotopic isometries between metric extensions are equal

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (M : Metric-Space l1 l2)
  (U : extension-Metric-Space l3 l4 M)
  (V : extension-Metric-Space l5 l6 M)
  (f g : isometry-extension-Metric-Space M U V)
  where

  htpy-isometry-extension-Metric-Space : UU (l3 ⊔ l5)
  htpy-isometry-extension-Metric-Space =
    ( map-metric-space-isometry-extension-Metric-Space M U V f ~
      map-metric-space-isometry-extension-Metric-Space M U V g)

  is-prop-htpy-isometry-extension-Metric-Space :
    is-prop htpy-isometry-extension-Metric-Space
  is-prop-htpy-isometry-extension-Metric-Space =
    is-prop-Π
      ( λ x →
        is-set-type-Metric-Space
          ( metric-space-extension-Metric-Space M V)
          ( map-metric-space-isometry-extension-Metric-Space M U V f x)
          ( map-metric-space-isometry-extension-Metric-Space M U V g x))

  htpy-prop-isometry-extension-Metric-Space : Prop (l3 ⊔ l5)
  htpy-prop-isometry-extension-Metric-Space =
    ( htpy-isometry-extension-Metric-Space ,
      is-prop-htpy-isometry-extension-Metric-Space)

  eq-htpy-isometry-extension-Metric-Space :
    htpy-isometry-extension-Metric-Space → f ＝ g
  eq-htpy-isometry-extension-Metric-Space f~g =
    eq-type-subtype
      ( coherence-triangle-prop-isometry-extension-Metric-Space M U V)
      ( eq-htpy-map-isometry-Metric-Space
        ( metric-space-extension-Metric-Space M U)
        ( metric-space-extension-Metric-Space M V)
        ( f~g))
```
