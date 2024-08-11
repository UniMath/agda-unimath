# Metric spaces

```agda
module metric-spaces.metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

A metric space is a set equipped a symmetric reflexive tight triangular
neighbourhood-relation.

## Definitions

### The property of being a metric neighbourhood-relation on a set

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Neighbourhood-Relation-Prop l2 (type-Set A))
  where

  is-metric-Neighbourhood : UU (l1 ⊔ l2)
  is-metric-Neighbourhood =
    ( is-symmetric-Neighbourhood B) ×
    ( is-reflexive-Neighbourhood B) ×
    ( is-tight-Neighbourhood B) ×
    ( is-triangular-Neighbourhood B)

  is-prop-is-metric-Neighbourhood : is-prop is-metric-Neighbourhood
  is-prop-is-metric-Neighbourhood =
    is-prop-product
      ( is-prop-is-symmetric-Neighbourhood B)
      ( is-prop-product
        ( is-prop-is-reflexive-Neighbourhood B)
        ( is-prop-product
          ( is-prop-Π
            ( λ x →
              is-prop-Π
              ( λ y → is-prop-Π (λ H → is-set-type-Set A x y))))
          ( is-prop-is-triangular-Neighbourhood B)))
```

### Metric structures over a set

```agda
module _
  {l1 : Level} (l2 : Level) (A : Set l1)
  where

  Metric-Structure : UU (l1 ⊔ lsuc l2)
  Metric-Structure =
    Σ ( Neighbourhood-Relation-Prop l2 (type-Set A))
      ( is-metric-Neighbourhood A)
```

### The type of metric spaces

```agda
Metric-Space : (l : Level) → UU (lsuc l)
Metric-Space l = Σ (Set l) (Metric-Structure l)

module _
  {l : Level} (M : Metric-Space l)
  where

  set-Metric-Space : Set l
  set-Metric-Space = pr1 M

  type-Metric-Space : UU l
  type-Metric-Space = type-Set set-Metric-Space

  is-set-type-Metric-Space : is-set type-Metric-Space
  is-set-type-Metric-Space = is-set-type-Set set-Metric-Space

  structure-Metric-Space : Metric-Structure l set-Metric-Space
  structure-Metric-Space = pr2 M

  neighbourhood-Metric-Space : Neighbourhood-Relation-Prop l type-Metric-Space
  neighbourhood-Metric-Space = pr1 structure-Metric-Space

  is-metric-neighbourhood-Metric-Space :
    is-metric-Neighbourhood set-Metric-Space neighbourhood-Metric-Space
  is-metric-neighbourhood-Metric-Space = pr2 structure-Metric-Space

  is-in-neighbourhood-Metric-Space : ℚ⁺ → Relation l type-Metric-Space
  is-in-neighbourhood-Metric-Space =
    is-in-Neighbourhood neighbourhood-Metric-Space

  is-symmetric-neighbourhood-Metric-Space :
    is-symmetric-Neighbourhood neighbourhood-Metric-Space
  is-symmetric-neighbourhood-Metric-Space =
    pr1 is-metric-neighbourhood-Metric-Space

  is-reflexive-neighbourhood-Metric-Space :
    is-reflexive-Neighbourhood neighbourhood-Metric-Space
  is-reflexive-neighbourhood-Metric-Space =
    pr1 (pr2 is-metric-neighbourhood-Metric-Space)

  is-tight-neighbourhood-Metric-Space :
    is-tight-Neighbourhood neighbourhood-Metric-Space
  is-tight-neighbourhood-Metric-Space =
    pr1 (pr2 (pr2 is-metric-neighbourhood-Metric-Space))

  is-triangular-neighbourhood-Metric-Space :
    is-triangular-Neighbourhood neighbourhood-Metric-Space
  is-triangular-neighbourhood-Metric-Space =
    pr2 (pr2 (pr2 is-metric-neighbourhood-Metric-Space))
```

## Properties

### Equal elements in a metric space are indistinguishable

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  indistinguishable-eq-Metric-Space :
    (x y : type-Metric-Space M) →
    x ＝ y →
    is-indistinguishable-Neighbourhood
      ( neighbourhood-Metric-Space M)
      ( x)
      ( y)
  indistinguishable-eq-Metric-Space x .x refl d =
    is-reflexive-neighbourhood-Metric-Space M d x
```

### Any set can be equipped with a metric structure

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Metric-Structure : Metric-Structure l A
  pr1 discrete-Metric-Structure d x y = Id-Prop A x y
  pr2 discrete-Metric-Structure =
    ( λ d x y H → inv H) ,
    ( λ d x → refl) ,
    ( λ x y H → H one-ℚ⁺) ,
    ( λ x y z d₁ d₂ H K → K ∙ H)

  discrete-Metric-Space : Metric-Space l
  discrete-Metric-Space = (A , discrete-Metric-Structure)
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
