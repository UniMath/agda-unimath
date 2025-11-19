# Cauchy dense metric extensions of pseudometric spaces

```agda
module metric-spaces.cauchy-dense-metric-extensions-of-pseudometric-spaces where
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
open import metric-spaces.cauchy-precompletion-of-pseudometric-spaces
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

A [metric extension](metric-spaces.metric-extensions-of-pseudometric-spaces.md)
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is called
{{#concept "Cauchy dense" Disambiguation="metric extension of a pseudometric space" Agda=is-cauchy-dense-Metric-Extension}}
if all the points of the target [metric space](metric-spaces.metric-spaces.md)
are [limits](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) of
images of
[cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
the pseudometric space.

## Definitions

### The property of being a limit point of the Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  (X : type-cauchy-precompletion-Pseudometric-Space P)
  (y : type-metric-space-Metric-Extension P M)
  where

  is-limit-cauchy-precompletion-prop-point-Metric-Extension :
    Prop (l1 ⊔ l2 ⊔ l4)
  is-limit-cauchy-precompletion-prop-point-Metric-Extension =
    Π-Prop
      ( cauchy-approximation-Pseudometric-Space P)
      ( λ x →
        Π-Prop
          ( is-in-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( X)
            ( x))
          ( λ x∈X →
            is-limit-map-metric-extension-prop-cauchy-approximation-Pseudometric-Space
              ( P)
              ( M)
              ( x)
              ( y)))

  is-limit-cauchy-precompletion-point-Metric-Extension : UU (l1 ⊔ l2 ⊔ l4)
  is-limit-cauchy-precompletion-point-Metric-Extension =
    type-Prop is-limit-cauchy-precompletion-prop-point-Metric-Extension
```

### Adherent points of a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  (y : type-metric-space-Metric-Extension P M)
  where

  is-adherent-point-Metric-Extension : UU (l1 ⊔ l2 ⊔ l4)
  is-adherent-point-Metric-Extension =
    Σ ( type-cauchy-precompletion-Pseudometric-Space P)
      ( λ X →
        is-limit-cauchy-precompletion-point-Metric-Extension P M X y)

  all-eq-is-adherent-point-Metric-Extension :
    (X X' : is-adherent-point-Metric-Extension) → X ＝ X'
  all-eq-is-adherent-point-Metric-Extension (X , lim-X) (X' , lim-X') =
    eq-type-subtype
      ( λ Y → is-limit-cauchy-precompletion-prop-point-Metric-Extension P M Y y)
      ( X＝X')
      where
        X＝X' : X ＝ X'
        X＝X' =
          let
            open
              do-syntax-trunc-Prop
                ( Id-Prop
                  ( set-Metric-Space
                    ( cauchy-precompletion-Pseudometric-Space P))
                  ( X)
                  ( X'))
          in do
            (x , x∈X) ←
              is-inhabited-class-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( X)
            (x' , x'∈X') ←
              is-inhabited-class-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( X')
            eq-set-quotient-sim-element-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P))
              ( X)
              ( X')
              ( x∈X)
              ( x'∈X')
              ( lemma-sim-is-limit-map-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M)
                ( y)
                ( x)
                ( x')
                ( lim-X x x∈X)
                ( lim-X' x' x'∈X'))

  is-prop-is-adherent-point-Metric-Extension :
    is-prop is-adherent-point-Metric-Extension
  is-prop-is-adherent-point-Metric-Extension =
    is-prop-all-elements-equal all-eq-is-adherent-point-Metric-Extension

  is-adherent-prop-point-Metric-Extension : Prop (l1 ⊔ l2 ⊔ l4)
  is-adherent-prop-point-Metric-Extension =
    ( is-adherent-point-Metric-Extension ,
      is-prop-is-adherent-point-Metric-Extension)
```

### The property of being a Cauchy dense metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  is-cauchy-dense-prop-Metric-Extension : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-dense-prop-Metric-Extension =
    Π-Prop
      ( type-metric-space-Metric-Extension P M)
      ( is-adherent-prop-point-Metric-Extension P M)

  is-cauchy-dense-Metric-Extension : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-dense-Metric-Extension =
    type-Prop is-cauchy-dense-prop-Metric-Extension

  is-prop-is-cauchy-dense-Metric-Extension :
    is-prop is-cauchy-dense-Metric-Extension
  is-prop-is-cauchy-dense-Metric-Extension =
    is-prop-type-Prop is-cauchy-dense-prop-Metric-Extension
```

## Properties

### The map from the target metric space of a Cauchy dense extension into the Cauchy precompletion is an isometry

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  (dense-M : is-cauchy-dense-Metric-Extension P M)
  where

  map-cauchy-precompletion-is-cauchy-dense-Metric-Extension :
    type-metric-space-Metric-Extension P M →
    type-cauchy-precompletion-Pseudometric-Space P
  map-cauchy-precompletion-is-cauchy-dense-Metric-Extension y =
    pr1 (dense-M y)

  is-limit-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension :
    (y : type-metric-space-Metric-Extension P M) →
    is-limit-cauchy-precompletion-point-Metric-Extension
      ( P)
      ( M)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension y)
      ( y)
  is-limit-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension y =
    pr2 (dense-M y)

  sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension :
    (y : type-metric-space-Metric-Extension P M) →
    (x : cauchy-approximation-Pseudometric-Space P) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension y)
      ( x) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( map-metric-extension-cauchy-approximation-Pseudometric-Space
        ( P)
        ( M)
        ( x))
      ( const-cauchy-approximation-Metric-Space
        ( metric-space-Metric-Extension P M)
        ( y))
  sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
    y x x∈X =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( map-metric-extension-cauchy-approximation-Pseudometric-Space P M x)
      ( y)
      ( is-limit-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
        ( y)
        ( x)
        ( x∈X))

  preserves-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension :
    is-short-function-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension)
  preserves-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension
    d X Y NXY (x , x∈fX) (y , y∈fY) =
    reflects-neighborhood-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( isometry-metric-extension-cauchy-approximation-Pseudometric-Space P M)
      ( d)
      ( x)
      ( y)
      ( Nxy)
    where

    fx~X :
      sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        ( map-metric-extension-cauchy-approximation-Pseudometric-Space P M x)
        ( const-cauchy-approximation-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( X))
    fx~X =
      sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
        ( X)
        ( x)
        ( x∈fX)

    fy~Y :
      sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        ( map-metric-extension-cauchy-approximation-Pseudometric-Space P M y)
        ( const-cauchy-approximation-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( Y))
    fy~Y =
      sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
        ( Y)
        ( y)
        ( y∈fY)

    Nxy :
      neighborhood-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        ( d)
        ( map-metric-extension-cauchy-approximation-Pseudometric-Space P M x)
        ( map-metric-extension-cauchy-approximation-Pseudometric-Space P M y)
    Nxy =
      reflects-neighborhood-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        { map-metric-extension-cauchy-approximation-Pseudometric-Space P M x}
        { const-cauchy-approximation-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( X)}
        { map-metric-extension-cauchy-approximation-Pseudometric-Space P M y}
        { const-cauchy-approximation-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( Y)}
        ( fx~X)
        ( fy~Y)
        ( d)
        ( preserves-neighborhood-map-cauchy-pseudocompletion-Pseudometric-Space
          ( pseudometric-space-Metric-Extension P M)
          ( d)
          ( X)
          ( Y)
          ( NXY))

  reflects-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension :
    ( d : ℚ⁺) →
    ( X Y : type-metric-space-Metric-Extension P M) →
    neighborhood-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( d)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension X)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension Y) →
    neighborhood-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( d)
      ( X)
      ( Y)
  reflects-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension
    d X Y NXY =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-Metric-Space
            ( metric-space-Metric-Extension P M)
            ( d)
            ( X)
            ( Y))
      in do
        ( u , lim-u) ←
          is-inhabited-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension X)

        ( v , lim-v) ←
          is-inhabited-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension Y)
        let
          fu~X :
            sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space
                ( metric-space-Metric-Extension P M))
              ( map-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M)
                ( u))
              ( const-cauchy-approximation-Metric-Space
                ( metric-space-Metric-Extension P M)
                ( X))
          fu~X =
            sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
              ( X)
              ( u)
              ( lim-u)

          fv~Y :
            sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space
                ( metric-space-Metric-Extension P M))
              ( map-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M)
                ( v))
              ( const-cauchy-approximation-Metric-Space
                ( metric-space-Metric-Extension P M)
                ( Y))
          fv~Y =
            sim-const-is-in-class-map-cauchy-precompletion-is-cauchy-dense-Metric-Extension
              ( Y)
              ( v)
              ( lim-v)

          Nuv :
            neighborhood-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space
                ( metric-space-Metric-Extension P M))
              ( d)
              ( map-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M)
                ( u))
              ( map-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M)
                ( v))
          Nuv =
            preserves-neighborhood-map-isometry-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( cauchy-pseudocompletion-Metric-Space
                ( metric-space-Metric-Extension P M))
              ( isometry-metric-extension-cauchy-approximation-Pseudometric-Space
                ( P)
                ( M))
              ( d)
              ( u)
              ( v)
              ( NXY (u , lim-u) (v , lim-v))

        reflects-neighborhood-map-isometry-Pseudometric-Space
          ( pseudometric-space-Metric-Extension P M)
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-Metric-Extension P M))
          ( isometry-cauchy-pseudocompletion-Metric-Space
            ( metric-space-Metric-Extension P M))
          ( d)
          ( X)
          ( Y)
          ( preserves-neighborhood-sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-Metric-Extension P M))
            { map-metric-extension-cauchy-approximation-Pseudometric-Space
              ( P)
              ( M)
              ( u)}
            { const-cauchy-approximation-Metric-Space
              ( metric-space-Metric-Extension P M)
              ( X)}
            { map-metric-extension-cauchy-approximation-Pseudometric-Space
              ( P)
              ( M)
              ( v)}
            { const-cauchy-approximation-Metric-Space
              ( metric-space-Metric-Extension P M)
              ( Y)}
            ( fu~X)
            ( fv~Y)
            ( d)
            ( Nuv))

  is-isometry-map-cauchy-precompletion-is-dense-Metric-Extension :
    is-isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension)
  is-isometry-map-cauchy-precompletion-is-dense-Metric-Extension d x y =
    ( ( preserves-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhood-map-cauchy-precompletion-is-dense-Metric-Extension
        ( d)
        ( x)
        ( y)))

  isometry-map-cauchy-precompletion-is-dense-Metric-Extension :
    isometry-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( cauchy-precompletion-Pseudometric-Space P)
  isometry-map-cauchy-precompletion-is-dense-Metric-Extension =
    ( map-cauchy-precompletion-is-cauchy-dense-Metric-Extension ,
      is-isometry-map-cauchy-precompletion-is-dense-Metric-Extension)
```

### The Cauchy precompletion of a pseudometric space is Cauchy dense

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where

  is-cauchy-dense-metric-extension-cauchy-precompletion-Pseudometric-Space :
    is-cauchy-dense-Metric-Extension
      ( P)
      ( metric-extension-cauchy-precompletion-Pseudometric-Space P)
  is-cauchy-dense-metric-extension-cauchy-precompletion-Pseudometric-Space X =
    ( X , is-limit-is-in-class-cauchy-precompletion-Pseudometric-Space P X)
```
