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
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
```

</details>

## Idea

A {{#concept "metric space" Agda=Metric-Space}} is a
[premetric space](metric-spaces.premetric-spaces.md) whose
[premetric](metric-spaces.premetric-structures.md) is reflexive symmetric local
and triangular.

## Definitions

### The property of being a metric premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-metric-prop-Premetric-Space : Prop (l1 ⊔ l2)
  is-metric-prop-Premetric-Space =
    is-metric-prop-Premetric (structure-Premetric-Space A)

  is-metric-Premetric-Space : UU (l1 ⊔ l2)
  is-metric-Premetric-Space =
    type-Prop is-metric-prop-Premetric-Space

  is-prop-is-metric-Premetric-Space :
    is-prop is-metric-Premetric-Space
  is-prop-is-metric-Premetric-Space =
    is-prop-type-Prop is-metric-prop-Premetric-Space
```

### The type of metric spaces

```agda
Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Space l1 l2 =
  type-subtype (is-metric-prop-Premetric-Space {l1} {l2})

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  premetric-Metric-Space : Premetric-Space l1 l2
  premetric-Metric-Space = pr1 M

  type-Metric-Space : UU l1
  type-Metric-Space =
    type-Premetric-Space premetric-Metric-Space

  structure-Metric-Space : Premetric l2 type-Metric-Space
  structure-Metric-Space =
    structure-Premetric-Space premetric-Metric-Space

  is-metric-structure-Metric-Space :
    is-metric-Premetric structure-Metric-Space
  is-metric-structure-Metric-Space = pr2 M

  neighbourhood-Metric-Space : ℚ⁺ → Relation l2 type-Metric-Space
  neighbourhood-Metric-Space =
    neighborhood-Premetric-Space premetric-Metric-Space

  is-reflexive-premetric-structure-Metric-Space :
    is-reflexive-Premetric structure-Metric-Space
  is-reflexive-premetric-structure-Metric-Space =
    pr1 is-metric-structure-Metric-Space

  is-symmetric-premetric-structure-Metric-Space :
    is-symmetric-Premetric structure-Metric-Space
  is-symmetric-premetric-structure-Metric-Space =
    pr1 (pr2 is-metric-structure-Metric-Space)

  is-local-premetric-structure-Metric-Space :
    is-local-Premetric structure-Metric-Space
  is-local-premetric-structure-Metric-Space =
    pr1 (pr2 (pr2 is-metric-structure-Metric-Space))

  is-triangular-premetric-structure-Metric-Space :
    is-triangular-Premetric structure-Metric-Space
  is-triangular-premetric-structure-Metric-Space =
    pr2 (pr2 (pr2 is-metric-structure-Metric-Space))

  is-tight-premetric-structure-Metric-Space :
    is-tight-Premetric structure-Metric-Space
  is-tight-premetric-structure-Metric-Space =
    is-tight-is-local-reflexive-Premetric
      structure-Metric-Space
      is-reflexive-premetric-structure-Metric-Space
      is-local-premetric-structure-Metric-Space

  is-monotonic-premetric-structure-Metric-Space :
    is-monotonic-Premetric structure-Metric-Space
  is-monotonic-premetric-structure-Metric-Space =
    is-monotonic-is-reflexive-triangular-Premetric
      structure-Metric-Space
      is-reflexive-premetric-structure-Metric-Space
      is-triangular-premetric-structure-Metric-Space

  is-set-type-Metric-Space : is-set type-Metric-Space
  is-set-type-Metric-Space =
    is-set-has-local-reflexive-Premetric
      structure-Metric-Space
      is-reflexive-premetric-structure-Metric-Space
      is-local-premetric-structure-Metric-Space

  set-Metric-Space : Set l1
  set-Metric-Space = (type-Metric-Space , is-set-type-Metric-Space)

  is-indistinguishable-prop-Metric-Space : Relation-Prop l2 type-Metric-Space
  is-indistinguishable-prop-Metric-Space =
    is-indistinguishable-prop-Premetric-Space premetric-Metric-Space

  is-indistinguishable-Metric-Space : Relation l2 type-Metric-Space
  is-indistinguishable-Metric-Space =
    is-indistinguishable-Premetric-Space premetric-Metric-Space

  is-prop-is-indistinguishable-Metric-Space :
    (x y : type-Metric-Space) →
    is-prop (is-indistinguishable-Metric-Space x y)
  is-prop-is-indistinguishable-Metric-Space =
    is-prop-is-indistinguishable-Premetric-Space premetric-Metric-Space
```

## Properties

### Indistiguishability in a metric space is equivalent to equality

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x y : type-Metric-Space M)
  where

  equiv-indistinguishable-eq-Metric-Space :
    (x ＝ y) ≃ is-indistinguishable-Metric-Space M x y
  equiv-indistinguishable-eq-Metric-Space =
    ( indistinguishable-eq-reflexive-Premetric
      ( structure-Metric-Space M)
      ( is-reflexive-premetric-structure-Metric-Space M)) ,
    ( is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric
      ( structure-Metric-Space M)
      ( is-reflexive-premetric-structure-Metric-Space M)
      ( is-local-premetric-structure-Metric-Space M)
      ( x)
      ( y))

  indistinguishable-eq-Metric-Space :
    x ＝ y → is-indistinguishable-Metric-Space M x y
  indistinguishable-eq-Metric-Space =
    map-equiv equiv-indistinguishable-eq-Metric-Space

  eq-indistinguishable-Metric-Space :
    is-indistinguishable-Metric-Space M x y → x ＝ y
  eq-indistinguishable-Metric-Space =
    map-inv-equiv equiv-indistinguishable-eq-Metric-Space
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology