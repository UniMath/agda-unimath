# Metric spaces

```agda
module metric-spaces.metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

A {{#concept "metric space" Agda=Metric-Space}} is a type equipped a symmetric
reflexive tight triangular
[neighbourhood-relation](metric-spaces.neighbourhood-relations.md).

## Definitions

### The property of being a metric neighbourhood-relation on a type

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : neighbourhood-Relation-Prop l2 A)
  where

  is-metric-neighbourhood : UU (l1 ⊔ l2)
  is-metric-neighbourhood =
    ( is-symmetric-neighbourhood B) ×
    ( is-reflexive-neighbourhood B) ×
    ( is-separating-neighbourhood B) ×
    ( is-triangular-neighbourhood B)

  is-prop-is-metric-neighbourhood : is-prop is-metric-neighbourhood
  is-prop-is-metric-neighbourhood =
    is-prop-product
      ( is-prop-is-symmetric-neighbourhood B)
      ( is-prop-product
        ( is-prop-is-reflexive-neighbourhood B)
        ( is-prop-product
          ( is-prop-is-separating-neighbourhood B)
          ( is-prop-is-triangular-neighbourhood B)))

  is-metric-prop-neighbourhood : Prop (l1 ⊔ l2)
  is-metric-prop-neighbourhood =
    is-metric-neighbourhood , is-prop-is-metric-neighbourhood
```

### Metric structures over a type

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Metric-Structure : UU (l1 ⊔ lsuc l2)
  Metric-Structure =
    Σ ( neighbourhood-Relation-Prop l2 A)
      ( is-metric-neighbourhood A)
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (S : Metric-Structure l2 A)
  where

  neighbourhood-Metric-Structure : neighbourhood-Relation-Prop l2 A
  neighbourhood-Metric-Structure = pr1 S

  is-metric-neighbourhood-Metric-Structure :
    is-metric-neighbourhood A neighbourhood-Metric-Structure
  is-metric-neighbourhood-Metric-Structure = pr2 S
```

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

### Any set can be equipped with a metric structure

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Metric-Structure : Metric-Structure l (type-Set A)
  pr1 discrete-Metric-Structure d = Id-Prop A
  pr2 discrete-Metric-Structure =
    ( λ d x y H → inv H) ,
    ( λ d x → refl) ,
    ( is-separating-is-tight-neighbourhood
      ( λ d → Id-Prop A)
      ( λ x y H → H one-ℚ⁺)) ,
    ( λ x y z d₁ d₂ H K → K ∙ H)

  discrete-Metric-Space : Metric-Space l
  discrete-Metric-Space = (type-Set A , discrete-Metric-Structure)
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
