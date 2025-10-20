# The pseudometric completion of a metric space

```agda
module metric-spaces.pseudometric-completion-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-completion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "pseudometric completion" Disambiguation="of a metric space" Agda=pseudometric-completion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is the
[pseudometric completion](metric-spaces.pseudometric-completion-of-pseudometric-spaces.md)
of its underlying [pseudometric space](metric-spaces.pseudometric-spaces.md):
the pseudometric space of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in `M` where two Cauchy approximations `x` and `y` are in a
[`d`-neighborhood](metric-spaces.rational-neighborhood-relations.md) of one
another if for all `δ ε : ℚ⁺`, `x δ` and `y ε` are in a
`(δ + ε + d)`-neighborhood of one another in `M`.

Any Cauchy approximation in the pseudometric completion has a
[limit](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md).
If the metric space is [complete](metric-spaces.complete-metric-spaces.md), it
is a [retract](foundation.retracts-of-types.md) of its pseudometric completion.

## Definition

### The pseudometric completion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  pseudometric-completion-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) l2
  pseudometric-completion-Metric-Space =
    pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### The pseudometric completion neighborhood relation on the type of Cauchy approximations in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  neighborhood-prop-pseudometric-completion-Metric-Space :
    Rational-Neighborhood-Relation l2
      (cauchy-approximation-Metric-Space M)
  neighborhood-prop-pseudometric-completion-Metric-Space =
    neighborhood-prop-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  neighborhood-pseudometric-completion-Metric-Space :
    ℚ⁺ → Relation l2 (cauchy-approximation-Metric-Space M)
  neighborhood-pseudometric-completion-Metric-Space =
    neighborhood-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

## Properties

### The neighborhood relation is reflexive

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-reflexive-neighborhood-pseudometric-completion-Metric-Space :
      (d : ℚ⁺) (x : cauchy-approximation-Metric-Space M) →
      neighborhood-pseudometric-completion-Metric-Space M d x x
    is-reflexive-neighborhood-pseudometric-completion-Metric-Space =
      is-reflexive-neighborhood-pseudometric-completion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The neighborhood relation is symmetric

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

    abstract
      is-symmetric-neighborhood-pseudometric-completion-Metric-Space :
        (d : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
        neighborhood-pseudometric-completion-Metric-Space M d x y →
        neighborhood-pseudometric-completion-Metric-Space M d y x
      is-symmetric-neighborhood-pseudometric-completion-Metric-Space =
        is-symmetric-neighborhood-pseudometric-completion-Pseudometric-Space
          ( pseudometric-Metric-Space M)
```

### The neighborhood relation is triangular

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-triangular-neighborhood-pseudometric-completion-Metric-Space :
      (x y z : cauchy-approximation-Metric-Space M) →
      (dxy dyz : ℚ⁺) →
      neighborhood-pseudometric-completion-Metric-Space M dyz y z →
      neighborhood-pseudometric-completion-Metric-Space M dxy x y →
      neighborhood-pseudometric-completion-Metric-Space
        ( M)
        ( dxy +ℚ⁺ dyz)
        ( x)
        ( z)
    is-triangular-neighborhood-pseudometric-completion-Metric-Space =
      is-triangular-neighborhood-pseudometric-completion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-saturated-neighborhood-pseudometric-completion-Metric-Space :
      ( ε : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
      ( (δ : ℚ⁺) →
        neighborhood-pseudometric-completion-Metric-Space
          ( M)
          ( ε +ℚ⁺ δ)
          ( x)
          ( y)) →
      neighborhood-pseudometric-completion-Metric-Space M ε x y
    is-saturated-neighborhood-pseudometric-completion-Metric-Space =
      is-saturated-neighborhood-pseudometric-completion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The isometry from a metric space to its pseudometric completion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-pseudometric-completion-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( pseudometric-completion-Metric-Space M)
  isometry-pseudometric-completion-Metric-Space =
    isometry-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  map-pseudometric-completion-Metric-Space :
    type-Metric-Space M → cauchy-approximation-Metric-Space M
  map-pseudometric-completion-Metric-Space =
    map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( pseudometric-completion-Metric-Space M)
      ( isometry-pseudometric-completion-Metric-Space)

  abstract
    is-isometry-map-pseudometric-completion-Metric-Space :
      is-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( pseudometric-completion-Metric-Space M)
        ( map-pseudometric-completion-Metric-Space)
    is-isometry-map-pseudometric-completion-Metric-Space =
      is-isometry-map-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( pseudometric-completion-Metric-Space M)
        ( isometry-pseudometric-completion-Metric-Space)
```

### Convergent Cauchy approximations are similar to constant Cauchy approximations in the pseudometric completion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : cauchy-approximation-Metric-Space M)
  (x : type-Metric-Space M)
  where

  abstract
    sim-const-is-limit-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space M u x →
      sim-Pseudometric-Space
        ( pseudometric-completion-Metric-Space M)
        ( u)
        ( const-cauchy-approximation-Metric-Space M x)
    sim-const-is-limit-cauchy-approximation-Metric-Space H d α β =
      monotonic-neighborhood-Metric-Space
        ( M)
        ( map-cauchy-approximation-Metric-Space M u α)
        ( x)
        ( α +ℚ⁺ β)
        ( α +ℚ⁺ β +ℚ⁺ d)
        ( le-left-add-ℚ⁺ (α +ℚ⁺ β) d)
        ( H α β)

    is-limit-sim-const-cauchy-approximation-Metric-Space :
      sim-Pseudometric-Space
        ( pseudometric-completion-Metric-Space M)
        ( u)
        ( const-cauchy-approximation-Metric-Space M x) →
      is-limit-cauchy-approximation-Metric-Space M u x
    is-limit-sim-const-cauchy-approximation-Metric-Space H α β =
      saturated-neighborhood-Metric-Space
        ( M)
        ( α +ℚ⁺ β)
        ( map-cauchy-approximation-Metric-Space M u α)
        ( x)
        ( λ d → H d α β)
```

### Any Cauchy approximation in the pseudometric completion of a metric space has a limit

```agda
module _
  { l1 l2 : Level} (M : Metric-Space l1 l2)
  ( U :
    cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M))
  where

  has-limit-cauchy-approximation-pseudometric-completion-Metric-Space :
    Σ ( cauchy-approximation-Metric-Space M)
      ( is-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-completion-Metric-Space M)
        ( U))
  has-limit-cauchy-approximation-pseudometric-completion-Metric-Space =
    has-limit-cauchy-approximation-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  lim-cauchy-approximation-pseudometric-completion-Metric-Space :
    cauchy-approximation-Metric-Space M
  lim-cauchy-approximation-pseudometric-completion-Metric-Space =
    pr1 has-limit-cauchy-approximation-pseudometric-completion-Metric-Space

  is-limit-lim-cauchy-approximation-pseudometric-completion-Metric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( U)
      ( lim-cauchy-approximation-pseudometric-completion-Metric-Space)
  is-limit-lim-cauchy-approximation-pseudometric-completion-Metric-Space =
    pr2 has-limit-cauchy-approximation-pseudometric-completion-Metric-Space
```

### The isometry from a Cauchy approximation in the pseudometric completion to its limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-lim-cauchy-approximation-pseudometric-completion-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space
        ( pseudometric-completion-Metric-Space M))
      ( pseudometric-completion-Metric-Space M)
  isometry-lim-cauchy-approximation-pseudometric-completion-Metric-Space =
    isometry-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### Any complete metric space is a short retract of its pseudometric completion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (is-complete-M : is-complete-Metric-Space M)
  where

  map-lim-pseudometric-completion-is-complete-Metric-Space :
    type-function-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( pseudometric-Metric-Space M)
  map-lim-pseudometric-completion-is-complete-Metric-Space =
    limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  is-limit-map-lim-pseudometric-completion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space u)
  is-limit-map-lim-pseudometric-completion-is-complete-Metric-Space =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  sim-const-map-lim-pseudometric-completion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    sim-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( u)
      ( const-cauchy-approximation-Metric-Space
        ( M)
        ( map-lim-pseudometric-completion-is-complete-Metric-Space u))
  sim-const-map-lim-pseudometric-completion-is-complete-Metric-Space u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space u)
      ( is-limit-map-lim-pseudometric-completion-is-complete-Metric-Space u)

  is-short-map-lim-pseudometric-completion-is-complete-Metric-Space :
    is-short-function-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( pseudometric-Metric-Space M)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space)
  is-short-map-lim-pseudometric-completion-is-complete-Metric-Space d x y Nxy =
    saturated-neighborhood-Metric-Space
      ( M)
      ( d)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space x)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space y)
      ( lemma-saturated-neighborhood-map-lim)
    where

      neighborhood-const-lim-x-y :
        neighborhood-Pseudometric-Space
          ( pseudometric-completion-Metric-Space M)
          ( d)
          ( const-cauchy-approximation-Metric-Space M
            ( map-lim-pseudometric-completion-is-complete-Metric-Space x))
          ( const-cauchy-approximation-Metric-Space M
            ( map-lim-pseudometric-completion-is-complete-Metric-Space y))
      neighborhood-const-lim-x-y =
        preserves-neighborhood-sim-Pseudometric-Space
          ( pseudometric-completion-Metric-Space M)
          { x}
          { const-cauchy-approximation-Metric-Space
            ( M)
            ( map-lim-pseudometric-completion-is-complete-Metric-Space x)}
          { y}
          { const-cauchy-approximation-Metric-Space
            ( M)
            ( map-lim-pseudometric-completion-is-complete-Metric-Space y)}
          ( sim-const-map-lim-pseudometric-completion-is-complete-Metric-Space
            ( x))
          ( sim-const-map-lim-pseudometric-completion-is-complete-Metric-Space
            ( y))
          ( d)
          ( Nxy)

      lemma-saturated-neighborhood-map-lim :
        (δ : ℚ⁺) →
        neighborhood-Metric-Space
          ( M)
          ( d +ℚ⁺ δ)
          ( map-lim-pseudometric-completion-is-complete-Metric-Space x)
          ( map-lim-pseudometric-completion-is-complete-Metric-Space y)
      lemma-saturated-neighborhood-map-lim δ =
        tr
          ( is-upper-bound-dist-Metric-Space
            ( M)
            ( map-lim-pseudometric-completion-is-complete-Metric-Space x)
            ( map-lim-pseudometric-completion-is-complete-Metric-Space y))
          ( ap (add-ℚ⁺' d) (eq-add-split-ℚ⁺ δ) ∙ commutative-add-ℚ⁺ δ d)
          ( neighborhood-const-lim-x-y
            ( left-summand-split-ℚ⁺ δ)
            ( right-summand-split-ℚ⁺ δ))

  short-map-lim-pseudometric-completion-is-complete-Metric-Space :
    short-function-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( pseudometric-Metric-Space M)
  short-map-lim-pseudometric-completion-is-complete-Metric-Space =
    ( map-lim-pseudometric-completion-is-complete-Metric-Space ,
      is-short-map-lim-pseudometric-completion-is-complete-Metric-Space)

  is-retraction-map-pseudometric-completion-is-complete-Metric-Space :
    ( map-lim-pseudometric-completion-is-complete-Metric-Space ∘
      map-pseudometric-completion-Metric-Space M) ~
    ( id)
  is-retraction-map-pseudometric-completion-is-complete-Metric-Space =
    is-retraction-limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  sim-map-lim-pseudometric-completion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    sim-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( u)
      ( map-pseudometric-completion-Metric-Space
        ( M)
        ( map-lim-pseudometric-completion-is-complete-Metric-Space u))
  sim-map-lim-pseudometric-completion-is-complete-Metric-Space u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-pseudometric-completion-is-complete-Metric-Space u)
      ( is-limit-map-lim-pseudometric-completion-is-complete-Metric-Space u)
```
