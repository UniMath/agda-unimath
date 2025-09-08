# The metric pseudocompletion of a pseudometric space

```agda
module metric-spaces.metric-pseudocompletion-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories

open import elementary-number-theory.positive-rational-numbers
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-completion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Metric pseudocompletion of pseudometric spaces.

## Definition

### The metric pseudocompletion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  metric-pseudocompletion-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-pseudocompletion-Pseudometric-Space =
    metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)

  pseudometric-metric-pseudocompletion-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-metric-pseudocompletion-Pseudometric-Space =
    pseudometric-Metric-Space
      metric-pseudocompletion-Pseudometric-Space

  type-metric-pseudocompletion-Pseudometric-Space : UU (l1 ⊔ l2)
  type-metric-pseudocompletion-Pseudometric-Space =
    type-Metric-Space metric-pseudocompletion-Pseudometric-Space
```

### The metric pseudocompletion of the pseudometric completion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    metric-pseudocompletion-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
```

## Properties

### The isometry from the pseudometric completion of a pseudometric space into its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
  isometry-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    isometry-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
```

### The isometry from a pseudometric space into its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-metric-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
  isometry-metric-pseudocompletion-Pseudometric-Space =
    comp-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-completion-Pseudometric-Space P)
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
      ( isometry-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
        ( P))
      ( isometry-pseudometric-completion-Pseudometric-Space P)
```

### The isometry from the pseudometric completion of the pseudometric completion into the metric pseudocompletion

```agda
module _
  { l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
  isometry-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space =
    comp-isometry-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( pseudometric-completion-Pseudometric-Space P)
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
      ( isometry-metric-quotient-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( isometry-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
        ( P))

  short-map-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space :
    short-function-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
  short-map-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space =
    short-isometry-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
      ( isometry-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space)
```

### The short map from the metric pseudocompletion of the pseudometric completion of a pseudometric space into its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    short-function-Metric-Space
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-Pseudometric-Space P)
  short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( short-map-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space
        ( P))

  map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    type-function-Metric-Space
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-Pseudometric-Space P)
  map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    map-short-function-Metric-Space
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)

  compute-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    ( X :
      type-metric-pseudocompletion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)) →
    ( x :
      cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( X)
      ( x) →
    map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space X ＝
    map-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
        ( P)
        ( x))
  compute-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( short-map-metric-pseudocompletion-pseudometric-completion²-Pseudometric-Space
        ( P))

  short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    short-function-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
  short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( short-isometry-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( pseudometric-metric-pseudocompletion-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space P))
        ( comp-isometry-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space P)
          ( pseudometric-completion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))
          ( pseudometric-metric-pseudocompletion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))
          ( isometry-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)))
          ( isometry-pseudometric-completion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))))

  map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    type-function-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
  map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    map-short-function-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)

  compute-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    (X : type-metric-pseudocompletion-Pseudometric-Space P) →
    (x : cauchy-approximation-Pseudometric-Space P) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( X)
      ( x) →
    map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
      ( X) ＝
    map-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( map-pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( x))
  compute-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( short-isometry-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( pseudometric-metric-pseudocompletion-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space P))
        ( comp-isometry-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space P)
          ( pseudometric-completion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))
          ( pseudometric-metric-pseudocompletion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))
          ( isometry-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)))
          ( isometry-pseudometric-completion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))))

  is-section-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    ( map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space ∘
      map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space) ~
    id
  is-section-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    X =
    let
      open
        do-syntax-trunc-Prop
          ( Id-Prop
            ( set-Metric-Space
              ( metric-pseudocompletion-Pseudometric-Space P))
            ( map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
              ( map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
                ( X)))
            ( X))
    in do
      ( x , x∈X) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space P)
          ( X)
      let
        map-inv-X =
          map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( X)

        compute-map-inv-X :
          map-inv-X ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( x))
        compute-map-inv-X =
          compute-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( X)
            ( x)
            ( x∈X)

        is-in-class-x :
          is-in-class-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-inv-X)
            ( map-pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( x))
        is-in-class-x =
          inv-tr
            ( λ Y →
              is-in-class-metric-quotient-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space
                  ( pseudometric-completion-Pseudometric-Space P))
                ( Y)
                ( map-pseudometric-completion-Pseudometric-Space
                  ( pseudometric-completion-Pseudometric-Space P)
                  ( x)))
            ( compute-map-inv-X)
            ( is-in-class-map-quotient-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P))
              ( map-pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x)))

        compute-map :
          map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( map-inv-X) ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( P)
              ( map-pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x)))
        compute-map =
          compute-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( map-inv-X)
            ( map-pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( x))
            ( is-in-class-x)

        compute-quotient-lim :
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( P)
              ( map-pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x))) ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( x)
        compute-quotient-lim =
          apply-effectiveness-quotient-map'
            ( equivalence-relation-sim-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( all-sim-is-limit-cauchy-approximation-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( map-pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x))
              ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                ( P)
                ( map-pseudometric-completion-Pseudometric-Space
                  ( pseudometric-completion-Pseudometric-Space P)
                  ( x)))
              ( x)
              ( is-limit-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                ( P)
                ( map-pseudometric-completion-Pseudometric-Space
                  ( pseudometric-completion-Pseudometric-Space P)
                  ( x)))
              ( is-limit-const-cauchy-approximation-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x)))

        compute-quotient-x :
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( x) ＝ X
        compute-quotient-x =
          eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( X)
            ( x∈X)

      ( compute-map ∙
        compute-quotient-lim ∙
        compute-quotient-x)

  is-retraction-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    ( map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space ∘
      map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)
      ~
    id
  is-retraction-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    X =
    let
      open
        do-syntax-trunc-Prop
          ( Id-Prop
            ( set-Metric-Space
              ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
                ( P)))
            ( map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
              ( map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
                ( X)))
            ( X))

    in do
      ( x , x∈X) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P))
          ( X)
      let
        map-X =
          map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( X)

        compute-map-X :
          map-X ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( P)
              ( x))
        compute-map-X =
          compute-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( X)
            ( x)
            ( x∈X)

        is-in-class-map-X :
          is-in-class-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( map-X)
            ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( P)
              ( x))
        is-in-class-map-X =
          inv-tr
            ( λ Y →
              is-in-class-metric-quotient-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( Y)
                ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                  ( P)
                  ( x)))
            ( compute-map-X)
            ( is-in-class-map-quotient-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                ( P)
                ( x)))

        compute-map-inv :
          map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( map-X) ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                ( P)
                ( x)))
        compute-map-inv =
          compute-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( map-X)
            ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( P)
              ( x))
            ( is-in-class-map-X)

        compute-map-quotient-lim :
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                ( P)
                ( x))) ＝
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( x)
        compute-map-quotient-lim =
          apply-effectiveness-quotient-map'
            ( equivalence-relation-sim-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)))
            ( symmetric-sim-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P))
              ( x)
              ( map-pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                  ( P)
                  ( x)))
              ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( x)
                ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                  ( P)
                  ( x))
                ( is-limit-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
                  ( P)
                  ( x))))

        compute-quotient-x :
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( x) ＝
          X
        compute-quotient-x =
          eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)))
            ( X)
            ( x∈X)

      ( compute-map-inv ∙
        compute-map-quotient-lim ∙
        compute-quotient-x)

  is-iso-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    is-iso-Precategory
      precategory-short-function-Metric-Space
      { metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P}
      { metric-pseudocompletion-Pseudometric-Space P}
      short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
  pr1
    is-iso-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    =
    short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
  pr2
    is-iso-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
    =
    ( ( eq-htpy-map-short-function-Metric-Space
        ( metric-pseudocompletion-Pseudometric-Space P)
        ( metric-pseudocompletion-Pseudometric-Space P)
        ( comp-short-function-Metric-Space
          ( metric-pseudocompletion-Pseudometric-Space P)
          ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( P))
          ( metric-pseudocompletion-Pseudometric-Space P)
          ( short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)
          ( short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space))
        ( short-id-Metric-Space
          ( metric-pseudocompletion-Pseudometric-Space P))
        ( is-section-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)) ,
      ( eq-htpy-map-short-function-Metric-Space
        ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
        ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
        ( comp-short-function-Metric-Space
          ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( P))
          ( metric-pseudocompletion-Pseudometric-Space P)
            ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
              ( P))
          ( short-map-inv-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)
          ( short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space))
        ( short-id-Metric-Space
          ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
            ( P)))
        ( is-retraction-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)))

  iso-metric-pseudocompeletion-pseudometric-completion-Pseudometric-Space :
    iso-Precategory
      ( precategory-short-function-Metric-Space)
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-Pseudometric-Space P)
  iso-metric-pseudocompeletion-pseudometric-completion-Pseudometric-Space =
    ( short-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space ,
      is-iso-map-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space)
```

### The equality between the metric pseudocompletion of the pseudometric completion of a pseudometric space and its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  eq-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space :
    ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P) ＝
    ( metric-pseudocompletion-Pseudometric-Space P)
  eq-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space =
    eq-isometric-equiv-Metric-Space'
      ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( map-equiv-isometric-equiv-iso-short-function-Metric-Space'
        ( metric-pseudocompletion-pseudometric-completion-Pseudometric-Space P)
        ( metric-pseudocompletion-Pseudometric-Space P)
        ( iso-metric-pseudocompeletion-pseudometric-completion-Pseudometric-Space
          ( P)))
```

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P))
  where

  is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u) →
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u)
  is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    sim-lift =
    let
      open
        do-syntax-trunc-Prop
          ( is-convergent-prop-cauchy-approximation-Metric-Space
            ( metric-pseudocompletion-Pseudometric-Space P)
            ( u))
    in do
      ( v , u~[v]) ← sim-lift
      let
        ( lim-v , is-lim-v) =
          has-limit-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( P)
            ( v)

        lim-u =
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( lim-v)

        is-lim[v]-lim-u :
          is-limit-cauchy-approximation-Metric-Space
            ( metric-quotient-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( v))
            ( lim-u)
        is-lim[v]-lim-u =
          preserves-limit-map-metric-quotient-cauchy-approximation-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( v)
            ( lim-v)
            ( is-lim-v)

        [lim-u] =
          const-cauchy-approximation-Metric-Space
            ( metric-pseudocompletion-Pseudometric-Space P)
            ( lim-u)

        u~[lim-u] :
          sim-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
            ( u)
            ( [lim-u])
        u~[lim-u] =
          transitive-sim-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
            ( u)
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( v))
            ( [lim-u])
            ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
              ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( v))
              ( lim-u)
              ( is-lim[v]-lim-u))
            ( u~[v])
      ( ( lim-u) ,
        ( is-limit-sim-const-cauchy-approximation-Pseudometric-Space
          ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
          ( u)
          ( lim-u)
          ( u~[lim-u])))

  iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ↔
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  pr1
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  pr2
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space

  equiv-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ≃
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  equiv-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    equiv-iff
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( metric-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( u))
      ( has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( u))
      ( is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space)
```

TO BE REMOVED. JUST HERE FOR EXPOSITORY PURPOSE.

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  lemma-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    ( u :
      cauchy-approximation-Metric-Space
        ( metric-pseudocompletion-Pseudometric-Space P)) →
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ↔
    exists
      ( cauchy-approximation-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( λ v →
        sim-prop-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space
            ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
          ( u)
          ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( v)))
  lemma-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
      ( P)
```
