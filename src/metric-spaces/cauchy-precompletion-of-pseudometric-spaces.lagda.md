# The Cauchy precompletion of a pseudometric space

```agda
module metric-spaces.cauchy-precompletion-of-pseudometric-spaces where
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

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
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
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Let `M` be a [pseudometric space](metric-spaces.pseudometric-spaces.md) and
`C M` denote its
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md);
the
{{#concept "Cauchy precompletion" Disambiguation="of a pseudometric space" Agda=cauchy-precompletion-Pseudometric-Space}}
of `M` is the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)

```text
[C M] = C M / ~
```

There are [isometries](metric-spaces.isometries-pseudometric-spaces.md)

```text
M → C M → [C M]
```

The Cauchy precompletion of the Cauchy pseudocompletion of a pseudometric space
is the Cauchy precompletion of the pseudometric space:

```text
[C (C M)] ＝ [C M]
```

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
in `[C M]`, `f : C [C M]` is
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) if
and only if it is
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) in
`C [C M]` to the
[pointwise quotient](metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces.md)
of some
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
`g : C (C M)`.

## Definition

### The Cauchy precompletion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  cauchy-precompletion-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  cauchy-precompletion-Pseudometric-Space =
    metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)

  pseudometric-cauchy-precompletion-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-cauchy-precompletion-Pseudometric-Space =
    pseudometric-Metric-Space
      cauchy-precompletion-Pseudometric-Space

  type-cauchy-precompletion-Pseudometric-Space : UU (l1 ⊔ l2)
  type-cauchy-precompletion-Pseudometric-Space =
    type-Metric-Space cauchy-precompletion-Pseudometric-Space
```

### The Cauchy precompletion of the Cauchy pseudocompletion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    cauchy-precompletion-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
```

## Properties

### The isometry from the Cauchy pseudocompletion of a pseudometric space into its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
  isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    isometry-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
```

### The isometry from a pseudometric space into its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-cauchy-precompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
  isometry-cauchy-precompletion-Pseudometric-Space =
    comp-isometry-Pseudometric-Space
      ( P)
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
        ( P))
      ( isometry-cauchy-pseudocompletion-Pseudometric-Space P)
```

### The isometry from the Cauchy pseudocompletion of the Cauchy pseudocompletion into the Cauchy precompletion

```agda
module _
  { l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  isometry-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
  isometry-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space =
    comp-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
        ( P))

  short-map-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space :
    short-function-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
  short-map-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space =
    short-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space)
```

### The short isomorphism from the Cauchy precompletion of the Cauchy pseudocompletion of a pseudometric space into its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    short-function-Metric-Space
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-Pseudometric-Space P)
  short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( cauchy-precompletion-Pseudometric-Space P)
      ( short-map-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space
        ( P))

  map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    type-function-Metric-Space
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-Pseudometric-Space P)
  map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    map-short-function-Metric-Space
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-Pseudometric-Space P)
      ( short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)

  compute-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    ( X :
      type-cauchy-precompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)) →
    ( x :
      cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( X)
      ( x) →
    map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space X ＝
    map-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
        ( P)
        ( x))
  compute-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( cauchy-precompletion-Pseudometric-Space P)
      ( short-map-cauchy-precompletion-cauchy-pseudocompletion²-Pseudometric-Space
        ( P))

  short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    short-function-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
  short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( comp-short-function-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( pseudometric-cauchy-precompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( short-map-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)))
        ( short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)))

  map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    type-function-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
  map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    map-short-function-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)

  compute-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    (X : type-cauchy-precompletion-Pseudometric-Space P) →
    (x : cauchy-approximation-Pseudometric-Space P) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( X)
      ( x) →
    map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
      ( X) ＝
    map-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( map-cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( x))
  compute-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( comp-short-function-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( pseudometric-cauchy-precompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P))
        ( short-map-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)))
        ( short-map-cauchy-pseudocompletion-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)))

  is-section-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    ( map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space ∘
      map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space) ~
    id
  is-section-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    X =
    let
      open
        do-syntax-trunc-Prop
          ( Id-Prop
            ( set-Metric-Space
              ( cauchy-precompletion-Pseudometric-Space P))
            ( map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
              ( map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
                ( X)))
            ( X))
    in do
      ( x , x∈X) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( X)
      let
        map-inv-X =
          map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( X)

        compute-map-inv-X :
          map-inv-X ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( x))
        compute-map-inv-X =
          compute-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( X)
            ( x)
            ( x∈X)

        is-in-class-x :
          is-in-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-inv-X)
            ( map-cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( x))
        is-in-class-x =
          inv-tr
            ( λ Y →
              is-in-class-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space
                  ( cauchy-pseudocompletion-Pseudometric-Space P))
                ( Y)
                ( map-cauchy-pseudocompletion-Pseudometric-Space
                  ( cauchy-pseudocompletion-Pseudometric-Space P)
                  ( x)))
            ( compute-map-inv-X)
            ( is-in-class-map-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P))
              ( map-cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x)))

        compute-map :
          map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( map-inv-X) ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( map-cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x)))
        compute-map =
          compute-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( map-inv-X)
            ( map-cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( x))
            ( is-in-class-x)

        compute-quotient-lim :
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( map-cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x))) ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( x)
        compute-quotient-lim =
          apply-effectiveness-quotient-map'
            ( equivalence-relation-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( all-sim-is-limit-cauchy-approximation-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( map-cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x))
              ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( P)
                ( map-cauchy-pseudocompletion-Pseudometric-Space
                  ( cauchy-pseudocompletion-Pseudometric-Space P)
                  ( x)))
              ( x)
              ( is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( P)
                ( map-cauchy-pseudocompletion-Pseudometric-Space
                  ( cauchy-pseudocompletion-Pseudometric-Space P)
                  ( x)))
              ( is-limit-const-cauchy-approximation-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x)))

        compute-quotient-x :
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( x) ＝ X
        compute-quotient-x =
          eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( X)
            ( x∈X)

      ( compute-map ∙
        compute-quotient-lim ∙
        compute-quotient-x)

  is-retraction-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    ( map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space ∘
      map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)
      ~
    id
  is-retraction-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    X =
    let
      open
        do-syntax-trunc-Prop
          ( Id-Prop
            ( set-Metric-Space
              ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
                ( P)))
            ( map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
              ( map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
                ( X)))
            ( X))

    in do
      ( x , x∈X) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P))
          ( X)
      let
        map-X =
          map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( X)

        compute-map-X :
          map-X ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( x))
        compute-map-X =
          compute-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( X)
            ( x)
            ( x∈X)

        is-in-class-map-X :
          is-in-class-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( map-X)
            ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( x))
        is-in-class-map-X =
          inv-tr
            ( λ Y →
              is-in-class-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( Y)
                ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                  ( P)
                  ( x)))
            ( compute-map-X)
            ( is-in-class-map-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( P)
                ( x)))

        compute-map-inv :
          map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( map-X) ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( P)
                ( x)))
        compute-map-inv =
          compute-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( map-X)
            ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
              ( P)
              ( x))
            ( is-in-class-map-X)

        compute-map-quotient-lim :
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                ( P)
                ( x))) ＝
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( x)
        compute-map-quotient-lim =
          apply-effectiveness-quotient-map'
            ( equivalence-relation-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)))
            ( symmetric-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P))
              ( x)
              ( map-cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                  ( P)
                  ( x)))
              ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( x)
                ( lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                  ( P)
                  ( x))
                ( is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
                  ( P)
                  ( x))))

        compute-quotient-x :
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( x) ＝
          X
        compute-quotient-x =
          eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)))
            ( X)
            ( x∈X)

      ( compute-map-inv ∙
        compute-map-quotient-lim ∙
        compute-quotient-x)

  is-iso-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    is-iso-Precategory
      precategory-short-function-Metric-Space
      { cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P}
      { cauchy-precompletion-Pseudometric-Space P}
      short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
  pr1
    is-iso-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    =
    short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
  pr2
    is-iso-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
    =
    ( ( eq-htpy-map-short-function-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)
        ( cauchy-precompletion-Pseudometric-Space P)
        ( comp-short-function-Metric-Space
          ( cauchy-precompletion-Pseudometric-Space P)
          ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( P))
          ( cauchy-precompletion-Pseudometric-Space P)
          ( short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)
          ( short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space))
        ( short-id-Metric-Space
          ( cauchy-precompletion-Pseudometric-Space P))
        ( is-section-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)) ,
      ( eq-htpy-map-short-function-Metric-Space
        ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
        ( comp-short-function-Metric-Space
          ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( P))
          ( cauchy-precompletion-Pseudometric-Space P)
            ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
              ( P))
          ( short-map-inv-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)
          ( short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space))
        ( short-id-Metric-Space
          ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
            ( P)))
        ( is-retraction-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)))

  iso-metric-pseudocompeletion-cauchy-pseudocompletion-Pseudometric-Space :
    iso-Precategory
      ( precategory-short-function-Metric-Space)
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-Pseudometric-Space P)
  iso-metric-pseudocompeletion-cauchy-pseudocompletion-Pseudometric-Space =
    ( short-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space ,
      is-iso-map-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)
```

### The equality between the Cauchy precompletion of the Cauchy pseudocompletion of a pseudometric space and its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  eq-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P) ＝
    ( cauchy-precompletion-Pseudometric-Space P)
  eq-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    eq-isometric-equiv-Metric-Space'
      ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-equiv-isometric-equiv-iso-short-function-Metric-Space'
        ( cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-precompletion-Pseudometric-Space P)
        ( iso-metric-pseudocompeletion-cauchy-pseudocompletion-Pseudometric-Space
          ( P)))
```

### Cauchy approximations similar to pointwise quotient of Cauchy approximations in the Cauchy pseudocompletion are convergent

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P))
  where

  is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u) →
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u)
  is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    sim-lift =
    let
      open
        do-syntax-trunc-Prop
          ( is-convergent-prop-cauchy-approximation-Metric-Space
            ( cauchy-precompletion-Pseudometric-Space P)
            ( u))
    in do
      ( v , u~[v]) ← sim-lift
      let
        ( lim-v , is-lim-v) =
          has-limit-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( v)

        lim-u =
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( lim-v)

        is-lim[v]-lim-u :
          is-limit-cauchy-approximation-Metric-Space
            ( metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( v))
            ( lim-u)
        is-lim[v]-lim-u =
          preserves-limit-map-metric-quotient-cauchy-approximation-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( v)
            ( lim-v)
            ( is-lim-v)

        [lim-u] =
          const-cauchy-approximation-Metric-Space
            ( cauchy-precompletion-Pseudometric-Space P)
            ( lim-u)

        u~[lim-u] :
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P))
            ( u)
            ( [lim-u])
        u~[lim-u] =
          transitive-sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P))
            ( u)
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( v))
            ( [lim-u])
            ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
              ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( v))
              ( lim-u)
              ( is-lim[v]-lim-u))
            ( u~[v])
      ( ( lim-u) ,
        ( is-limit-sim-const-cauchy-approximation-Pseudometric-Space
          ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
          ( u)
          ( lim-u)
          ( u~[lim-u])))

  iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u) ↔
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  pr1
    iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  pr2
    iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space

  equiv-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u) ≃
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  equiv-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    equiv-iff
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space)
```
