# Metric spaces

```agda
module metric-spaces.metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-structures
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

A {{#concept "metric space" Agda=Metric-Space}} is a type equipped a
[metric structure](metric-spaces.metric-structures.md): a symmetric reflexive
separating triangular
[neighbourhood-relation](metric-spaces.neighbourhood-relations.md).

## Definitions

### The type of metric spaces

```agda
Metric-Space : (l : Level) → UU (lsuc l)
Metric-Space l = Σ (UU l) (Metric-Structure l)

module _
  {l : Level} (M : Metric-Space l)
  where

  type-Metric-Space : UU l
  type-Metric-Space = pr1 M

  structure-Metric-Space : Metric-Structure l type-Metric-Space
  structure-Metric-Space = pr2 M

  neighbourhood-Metric-Space : neighbourhood-Relation-Prop l type-Metric-Space
  neighbourhood-Metric-Space = pr1 structure-Metric-Space

  is-metric-neighbourhood-Metric-Space :
    is-metric-neighbourhood type-Metric-Space neighbourhood-Metric-Space
  is-metric-neighbourhood-Metric-Space = pr2 structure-Metric-Space

  is-in-neighbourhood-Metric-Space : ℚ⁺ → Relation l type-Metric-Space
  is-in-neighbourhood-Metric-Space =
    is-in-neighbourhood neighbourhood-Metric-Space

  is-symmetric-neighbourhood-Metric-Space :
    is-symmetric-neighbourhood neighbourhood-Metric-Space
  is-symmetric-neighbourhood-Metric-Space =
    pr1 is-metric-neighbourhood-Metric-Space

  is-reflexive-neighbourhood-Metric-Space :
    is-reflexive-neighbourhood neighbourhood-Metric-Space
  is-reflexive-neighbourhood-Metric-Space =
    pr1 (pr2 is-metric-neighbourhood-Metric-Space)

  is-separating-neighbourhood-Metric-Space :
    is-separating-neighbourhood neighbourhood-Metric-Space
  is-separating-neighbourhood-Metric-Space =
    pr1 (pr2 (pr2 is-metric-neighbourhood-Metric-Space))

  is-tight-neighbourhood-Metric-Space :
    is-tight-neighbourhood neighbourhood-Metric-Space
  is-tight-neighbourhood-Metric-Space =
    is-tight-is-separating-reflexive-neighbourhood
      neighbourhood-Metric-Space
      is-separating-neighbourhood-Metric-Space
      is-reflexive-neighbourhood-Metric-Space

  is-triangular-neighbourhood-Metric-Space :
    is-triangular-neighbourhood neighbourhood-Metric-Space
  is-triangular-neighbourhood-Metric-Space =
    pr2 (pr2 (pr2 is-metric-neighbourhood-Metric-Space))

  is-set-type-Metric-Space : is-set type-Metric-Space
  is-set-type-Metric-Space =
    is-set-has-separating-reflexive-neighbourhood
      neighbourhood-Metric-Space
      is-separating-neighbourhood-Metric-Space
      is-reflexive-neighbourhood-Metric-Space

  set-Metric-Space : Set l
  set-Metric-Space = (type-Metric-Space , is-set-type-Metric-Space)
```

## Properties

### Equal elements in a metric space are indistinguishable

```agda
module _
  {l : Level} (M : Metric-Space l) (x y : type-Metric-Space M)
  where

  indistinguishable-eq-Metric-Space :
    x ＝ y →
    is-indistinguishable-in-neighbourhood
      ( neighbourhood-Metric-Space M)
      ( x)
      ( y)
  indistinguishable-eq-Metric-Space =
    indistinguishable-eq-reflexive-neighbourhood
      ( neighbourhood-Metric-Space M)
      ( is-reflexive-neighbourhood-Metric-Space M)
      ( x)
      ( y)
```

### Indistiguishability in a metric space is equivalent to equality

```agda
module _
  {l : Level} (M : Metric-Space l) (x y : type-Metric-Space M)
  where

  is-equiv-indistinguishable-eq-Metric-Space :
    is-equiv (indistinguishable-eq-Metric-Space M x y)
  is-equiv-indistinguishable-eq-Metric-Space =
    is-equiv-indistinguishable-eq-separating-reflexive-neighbourhood
      ( neighbourhood-Metric-Space M)
      ( is-separating-neighbourhood-Metric-Space M)
      ( is-reflexive-neighbourhood-Metric-Space M)
      ( x)
      ( y)
```

### Any set is a discrete metric space

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Metric-Space : Metric-Space l
  discrete-Metric-Space = (type-Set A , discrete-Metric-Structure A)
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
