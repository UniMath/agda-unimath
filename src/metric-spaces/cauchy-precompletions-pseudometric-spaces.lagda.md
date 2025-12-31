# The Cauchy precompletion of a pseudometric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-precompletions-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories

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
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-complete-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-pseudometric-spaces
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

Any [short map](metric-spaces.short-functions-pseudometric-spaces.md) (resp.
isometry) from a pseudometric space in a complete metric space factors as a
short map (resp. isometry) through the Cauchy precompletion of its domain. This
is the
{{#concept "universal property" Disambiguation="of the Cauchy precompletion of a pseudometric space"}}
of the Cauchy precompletion.

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

  map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space P →
    type-cauchy-precompletion-Pseudometric-Space P
  map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space)

  extension-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space :
    extension-Pseudometric-Space
      ( l1 ⊔ l2)
      ( l1 ⊔ l2)
      ( cauchy-pseudocompletion-Pseudometric-Space P)
  pr1
    extension-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    pseudometric-cauchy-precompletion-Pseudometric-Space P
  pr2
    extension-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space =
    isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
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

  map-isometry-cauchy-precompletion-Pseudometric-Space :
    type-Pseudometric-Space P →
    type-cauchy-precompletion-Pseudometric-Space P
  map-isometry-cauchy-precompletion-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-cauchy-precompletion-Pseudometric-Space)
```

## Properties

### The isometry from the cauchy pseudocompletiom of a pseudometric space into its precompletion is surjective

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  is-surjective-map-isometry-cauchy-precompletion-Pseudometric-Space :
    is-surjective
      ( map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
        ( P))
  is-surjective-map-isometry-cauchy-precompletion-Pseudometric-Space X =
    map-tot-exists
      ( λ x x∈X →
        eq-map-is-in-class-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( X)
          ( x∈X))
      ( is-inhabited-class-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( X))
```

### Induced short map from the Cauchy precompletion to a complete metric space

```agda
module _
  { l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  ( C : Complete-Metric-Space l3 l4)
  where

  short-map-short-function-complete-metric-space-cauchy-precompletion-Pseudometric-Space :
    short-function-Pseudometric-Space
      ( P)
      ( pseudometric-space-Complete-Metric-Space C) →
    short-function-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
        ( metric-space-Complete-Metric-Space C)
  short-map-short-function-complete-metric-space-cauchy-precompletion-Pseudometric-Space
    f =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( metric-space-Complete-Metric-Space C)
      ( comp-short-function-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space C))
        ( pseudometric-space-Complete-Metric-Space C)
        ( short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( metric-space-Complete-Metric-Space C)
          ( is-complete-metric-space-Complete-Metric-Space C))
        ( short-map-cauchy-approximation-short-function-Pseudometric-Space
          ( P)
          ( pseudometric-space-Complete-Metric-Space C)
          ( f)))
```

### Induced isometry from the Cauchy precompletion into a complete metric space

```agda
module _
  { l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  ( C : Complete-Metric-Space l3 l4)
  where

  isometry-map-isometry-complete-metric-space-cauchy-precompletion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-Complete-Metric-Space C) →
    isometry-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( metric-space-Complete-Metric-Space C)
  isometry-map-isometry-complete-metric-space-cauchy-precompletion-Pseudometric-Space
    f =
    isometry-map-isometry-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( metric-space-Complete-Metric-Space C)
      ( comp-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space C))
        ( pseudometric-space-Complete-Metric-Space C)
        ( isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( metric-space-Complete-Metric-Space C)
          ( is-complete-metric-space-Complete-Metric-Space C))
        ( isometry-map-cauchy-approximation-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-space-Complete-Metric-Space C)
          ( f)))
```

### The image of a Cauchy approximation in the Cauchy precompletion converges to its image by the quotient map

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space P)
  where

  sim-const-map-isometry-cauchy-precompletion-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P))
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( const-cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)
        ( map-metric-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( u)))
  sim-const-map-isometry-cauchy-precompletion-Pseudometric-Space d α β =
    preserves-neighborhoods-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
      ( isometry-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P))
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( const-cauchy-approximation-Pseudometric-Space
        ( P)
        ( map-cauchy-approximation-Pseudometric-Space P u α))
      ( u)
      ( λ ε δ →
        monotonic-neighborhood-Pseudometric-Space
          ( P)
          ( map-cauchy-approximation-Pseudometric-Space P u α)
          ( map-cauchy-approximation-Pseudometric-Space P u δ)
          ( α +ℚ⁺ δ)
          ( ( ε +ℚ⁺ δ) +ℚ⁺ (α +ℚ⁺ β +ℚ⁺ d))
          ( lemma-le α δ ε β d)
          ( is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
            ( P)
            ( u)
            ( α)
            ( δ)))
      where

      lemma-le :
        (a b c d e : ℚ⁺) →
        le-ℚ⁺
          ( a +ℚ⁺ b)
          ( (c +ℚ⁺ b) +ℚ⁺ (a +ℚ⁺ d +ℚ⁺ e))
      lemma-le a b c d e =
        tr
          ( λ u → le-ℚ⁺ u ((c +ℚ⁺ b) +ℚ⁺ (a +ℚ⁺ d +ℚ⁺ e)))
          ( commutative-add-ℚ⁺ b a)
          ( preserves-le-add-ℚ
            { rational-ℚ⁺ b}
            { rational-ℚ⁺ (c +ℚ⁺ b)}
            { rational-ℚ⁺ a}
            { rational-ℚ⁺ (a +ℚ⁺ d +ℚ⁺ e)}
            ( le-right-add-ℚ⁺ c b)
            ( transitive-le-ℚ⁺
              ( a)
              ( a +ℚ⁺ d)
              ( a +ℚ⁺ d +ℚ⁺ e)
              ( le-left-add-ℚ⁺ (a +ℚ⁺ d) e)
              ( le-left-add-ℚ⁺ a d)))

  is-limit-map-isometry-cauchy-pseudocompletion-cauchy-precompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( map-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
  is-limit-map-isometry-cauchy-pseudocompletion-cauchy-precompletion-Pseudometric-Space
    =
    is-limit-sim-const-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
          ( P))
        ( u))
      ( sim-const-map-isometry-cauchy-precompletion-Pseudometric-Space)
```

### Any point of the Cauchy precompletion is the limit of the image of a Cauchy approximation

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  is-limit-is-in-class-cauchy-precompletion-Pseudometric-Space :
    (X : type-cauchy-precompletion-Pseudometric-Space P) →
    (x : cauchy-approximation-Pseudometric-Space P) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( X)
      ( x) →
    is-limit-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( x))
      ( X)
  is-limit-is-in-class-cauchy-precompletion-Pseudometric-Space X x x∈X =
    tr
      ( is-limit-cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)
        ( map-cauchy-approximation-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
          ( isometry-cauchy-precompletion-Pseudometric-Space P)
          ( x)))
      ( eq-map-is-in-class-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( X)
        ( x∈X))
      ( is-limit-map-isometry-cauchy-pseudocompletion-cauchy-precompletion-Pseudometric-Space
        ( P)
        ( x))
```
