# Small pointed types

```agda
module structured-types.small-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.small-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-types
```

</details>

## Idea

A [pointed type](structured-types.pointed-types.md) is said to be {{#concept "small" Disambiguation="pointed type" Agda=is-small-Pointed-Type}} is its underlying type is [small](foundation.small-types.md). Equivalently, we say that a type is {{#concept "pointedly small" Agda=is-pointedly-small-Pointed-Type}} if it comes equipped with an element of type

```text
  Σ (Y : Pointed-Type l), X ≃∗ Y
```

The difference between small pointed types and pointedly small pointed types is that the notion of small pointed type is unpointed, and therefore potentially easier to establish. It is immediate that a pointedly small type is small. For the converse, note that if `X` is small, and `Y : 𝒰` comes equipped with an [equivalence](foundation-core.equivalences.md) `e : type-Pointed-Type X ≃ Y`, then we take `e * : Y` to be the base point, and it is immediate that `e` is a [pointed equivalence](structured-types.pointed-equivalences.md).

## Definitions

### Small pointed types

```agda
module _
  {l1 : Level} (l2 : Level) (X : Pointed-Type l1)
  where

  is-small-prop-Pointed-Type : Prop (l1 ⊔ lsuc l2)
  is-small-prop-Pointed-Type = is-small-Prop l2 (type-Pointed-Type X)

  is-small-Pointed-Type : UU (l1 ⊔ lsuc l2)
  is-small-Pointed-Type = is-small l2 (type-Pointed-Type X)

  is-prop-is-small-Pointed-Type : is-prop is-small-Pointed-Type
  is-prop-is-small-Pointed-Type = is-prop-is-small l2 (type-Pointed-Type X)
```

### Pointedly small types

```agda
module _
  {l1 : Level} (l2 : Level) (X : Pointed-Type l1)
  where

  is-pointedly-small-Pointed-Type : UU (l1 ⊔ lsuc l2)
  is-pointedly-small-Pointed-Type =
    Σ (Pointed-Type l2) (λ Y → X ≃∗ Y)

module _
  {l1 l2 : Level} (X : Pointed-Type l1)
  (H : is-pointedly-small-Pointed-Type l2 X)
  where

  pointed-type-is-pointedly-small-Pointed-Type : Pointed-Type l2
  pointed-type-is-pointedly-small-Pointed-Type = pr1 H

  type-is-pointedly-small-Pointed-Type : UU l2
  type-is-pointedly-small-Pointed-Type =
    type-Pointed-Type pointed-type-is-pointedly-small-Pointed-Type

  point-is-pointedly-small-Pointed-Type :
    type-is-pointedly-small-Pointed-Type
  point-is-pointedly-small-Pointed-Type =
    point-Pointed-Type pointed-type-is-pointedly-small-Pointed-Type

  pointed-equiv-is-pointedly-small-Pointed-Type :
    X ≃∗ pointed-type-is-pointedly-small-Pointed-Type
  pointed-equiv-is-pointedly-small-Pointed-Type = pr2 H
```

## Properties

### Being pointedly small is a property

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1)
  where

  is-prop-is-pointedly-small-Pointed-Type :
    is-prop (is-pointedly-small-Pointed-Type l2 X)
  is-prop-is-pointedly-small-Pointed-Type =
    is-prop-is-inhabited
      ( λ (Y , e) →
        is-prop-equiv'
          ( equiv-tot (λ Z → equiv-comp-pointed-equiv' e))
          ( is-prop-is-contr (is-torsorial-pointed-equiv Y)))

module _
  {l1 : Level} (l2 : Level) (X : Pointed-Type l1)
  where
  
  is-pointedly-small-prop-Pointed-Type : Prop (l1 ⊔ lsuc l2)
  pr1 is-pointedly-small-prop-Pointed-Type =
    is-pointedly-small-Pointed-Type l2 X
  pr2 is-pointedly-small-prop-Pointed-Type =
    is-prop-is-pointedly-small-Pointed-Type X
```

### A pointed type is small if and only if it is pointedly small

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1)
  where

  is-pointedly-small-is-small-Pointed-Type :
    is-small-Pointed-Type l2 X → is-pointedly-small-Pointed-Type l2 X
  pr1 (pr1 (is-pointedly-small-is-small-Pointed-Type (Y , e))) =
    Y
  pr2 (pr1 (is-pointedly-small-is-small-Pointed-Type (Y , e))) =
    map-equiv e (point-Pointed-Type X)
  pr1 (pr2 (is-pointedly-small-is-small-Pointed-Type (Y , e))) =
    e
  pr2 (pr2 (is-pointedly-small-is-small-Pointed-Type (Y , e))) =
    refl

  is-small-is-pointedly-small-Pointed-Type :
    is-pointedly-small-Pointed-Type l2 X → is-small-Pointed-Type l2 X
  pr1 (is-small-is-pointedly-small-Pointed-Type (Y , e)) =
    type-Pointed-Type Y
  pr2 (is-small-is-pointedly-small-Pointed-Type (Y , e)) =
    equiv-pointed-equiv e
```
