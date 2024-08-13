# Dependent products of metric spaces

```agda
module metric-spaces.dependent-products-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.uniform-continuity-functions-metric-spaces
```

</details>

## Idea

Dependent products of [metric spaces](metric-spaces.metric-spaces.md) inherit a
{{#concept "product metric structure" Agda=Π-Metric-Structure}} where
[`d`-neighbourhoods](metric-spaces.neighbourhood-relations.md) are the products
of neighbourhoods over each metric space.

## Definitions

### Product structure of metric spaces

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Metric-Space l2)
  where

  type-Π-Metric-Space : UU (l1 ⊔ l2)
  type-Π-Metric-Space = (x : A) → type-Metric-Space (P x)

  neighbourhood-Π-Metric-Space :
    neighbourhood-Relation-Prop (l1 ⊔ l2) type-Π-Metric-Space
  neighbourhood-Π-Metric-Space d f g =
    Π-Prop A (λ a → neighbourhood-Metric-Space (P a) d (f a) (g a))

  is-tight-neighbourhood-Π-Metric-Space :
    is-tight-neighbourhood neighbourhood-Π-Metric-Space
  is-tight-neighbourhood-Π-Metric-Space f g H =
    eq-htpy
      ( λ a →
        is-tight-neighbourhood-Metric-Space
          ( P a)
          ( f a)
          ( g a)
          ( λ d → H d a))

  Π-Metric-Structure : Metric-Structure (l1 ⊔ l2) type-Π-Metric-Space
  pr1 Π-Metric-Structure = neighbourhood-Π-Metric-Space
  pr2 Π-Metric-Structure =
    ( λ d f g H a →
      is-symmetric-neighbourhood-Metric-Space
        ( P a)
        ( d)
        ( f a)
        ( g a)
        ( H a)) ,
    ( λ d f a →
      is-reflexive-neighbourhood-Metric-Space
        ( P a)
        ( d)
        ( f a)) ,
    ( is-separating-is-tight-neighbourhood
      ( neighbourhood-Π-Metric-Space)
      ( is-tight-neighbourhood-Π-Metric-Space)) ,
    ( λ f g h d₁ d₂ H K a →
      is-triangular-neighbourhood-Metric-Space
        ( P a)
        ( f a)
        ( g a)
        ( h a)
        ( d₁)
        ( d₂)
        ( H a)
        ( K a))
```

### Product of metric spaces

```agda
module _
  {l1 l2 : Level}
  where

  Π-Metric-Space' :
    (A : UU l1) → (P : A → Metric-Space l2) → Metric-Space (l1 ⊔ l2)
  Π-Metric-Space' A P = (type-Π-Metric-Space A P , Π-Metric-Structure A P)

  Π-Metric-Space :
    (A : Metric-Space l1) →
    (P : type-Metric-Space A → Metric-Space l2) →
    Metric-Space (l1 ⊔ l2)
  Π-Metric-Space A = Π-Metric-Space' (type-Metric-Space A)
```

## Properties

### The evaluation maps on a product metric space are uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Metric-Space l2) (x : A)
  where

  is-uniformly-continuous-ev-Π-Metric-Space :
    is-uniformly-continuous-function-Metric-Space
      ( Π-Metric-Space' A P)
      ( P x)
      ( λ f → f x)
  is-uniformly-continuous-ev-Π-Metric-Space ε = (ε , λ f g H → H x)
```
