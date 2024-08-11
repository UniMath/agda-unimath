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
```

</details>

## Idea

Dependent products of metric spaces inherit a product metric structure

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Metric-Space l2)
  where

  set-Π-Metric-Space : Set (l1 ⊔ l2)
  set-Π-Metric-Space = Π-Set' A (set-Metric-Space ∘ P)

  Π-Metric-Structure : Metric-Structure (l1 ⊔ l2) set-Π-Metric-Space
  pr1 Π-Metric-Structure d f g =
    Π-Prop A
      ( λ a →
        neighbourhood-Metric-Space (P a) d (f a) (g a))
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
    ( λ f g H →
      eq-htpy
        ( λ a →
          is-tight-neighbourhood-Metric-Space
            ( P a)
            ( f a)
            ( g a)
            ( λ d → H d a))) ,
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

  Π-Metric-Space' : Metric-Space (l1 ⊔ l2)
  Π-Metric-Space' = (set-Π-Metric-Space , Π-Metric-Structure)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1)
  (P : type-Metric-Space A → Metric-Space l2)
  where

  Π-Metric-Space : Metric-Space (l1 ⊔ l2)
  Π-Metric-Space = Π-Metric-Space' (type-Metric-Space A) P
```
