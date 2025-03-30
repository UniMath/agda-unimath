# Products of metric spaces

```agda
module metric-spaces.products-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.sets
open import foundation.conjunction
open import foundation.universe-levels
open import foundation.cartesian-product-types
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import foundation.equality-cartesian-product-types
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A pair of [metric spaces](metric-spaces.metric-spaces.md) induces a metric space
over the [Cartesian product](foundation.cartesian-product-types.md) of the
carrier types of its arguments.

## Definitions

### Products of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  type-product-Metric-Space : UU (l1 ⊔ l3)
  type-product-Metric-Space = type-Metric-Space A × type-Metric-Space B

  structure-product-Metric-Space : Premetric (l2 ⊔ l4) type-product-Metric-Space
  structure-product-Metric-Space d (a1 , b1) (a2 , b2) =
    structure-Metric-Space A d a1 a2 ∧ structure-Metric-Space B d b1 b2

  is-reflexive-structure-product-Metric-Space :
    is-reflexive-Premetric structure-product-Metric-Space
  is-reflexive-structure-product-Metric-Space d (a , b) =
    ( is-reflexive-structure-Metric-Space A d a ,
      is-reflexive-structure-Metric-Space B d b)

  is-symmetric-structure-product-Metric-Space :
    is-symmetric-Premetric structure-product-Metric-Space
  is-symmetric-structure-product-Metric-Space
    d (a1 , b1) (a2 , b2) (a1~a2 , b1~b2) =
      ( is-symmetric-structure-Metric-Space A d a1 a2 a1~a2 ,
        is-symmetric-structure-Metric-Space B d b1 b2 b1~b2)

  is-triangular-structure-product-Metric-Space :
    is-triangular-Premetric structure-product-Metric-Space
  is-triangular-structure-product-Metric-Space
    (a1 , b1) (a2 , b2) (a3 , b3) d12 d23 (a1~a2 , b1~b2) (a2~a3 , b2~b3) =
      ( is-triangular-structure-Metric-Space A a1 a2 a3 d12 d23 a1~a2 a2~a3 ,
        is-triangular-structure-Metric-Space B b1 b2 b3 d12 d23 b1~b2 b2~b3)


  is-local-structure-product-Metric-Space :
    is-local-Premetric structure-product-Metric-Space
  is-local-structure-product-Metric-Space =
    is-local-is-tight-Premetric
      ( structure-product-Metric-Space)
      ( λ (a1 , b1) (a2 , b2) ind-ab1-ab2 →
        eq-pair
          ( is-tight-structure-Metric-Space A a1 a2 (pr1 ∘ ind-ab1-ab2))
          ( is-tight-structure-Metric-Space B b1 b2 (pr2 ∘ ind-ab1-ab2)))

  is-pseudometric-structure-product-Metric-Space :
    is-pseudometric-Premetric structure-product-Metric-Space
  is-pseudometric-structure-product-Metric-Space =
    is-reflexive-structure-product-Metric-Space ,
    is-symmetric-structure-product-Metric-Space ,
    is-triangular-structure-product-Metric-Space

  is-metric-structure-product-Metric-Space :
    is-metric-Premetric structure-product-Metric-Space
  is-metric-structure-product-Metric-Space =
    is-pseudometric-structure-product-Metric-Space ,
    is-local-structure-product-Metric-Space

  product-Metric-Space : Metric-Space (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 product-Metric-Space =
    ( type-product-Metric-Space , structure-product-Metric-Space)
  pr2 product-Metric-Space = is-metric-structure-product-Metric-Space
```

## Properties

### The projection maps on a product metric space are short

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  is-short-pr1-product-Metric-Space :
    is-short-function-Metric-Space (product-Metric-Space A B) A pr1
  is-short-pr1-product-Metric-Space _ _ _ = pr1

  is-short-pr2-product-Metric-Space :
    is-short-function-Metric-Space (product-Metric-Space A B) B pr2
  is-short-pr2-product-Metric-Space _ _ _ = pr2
```
