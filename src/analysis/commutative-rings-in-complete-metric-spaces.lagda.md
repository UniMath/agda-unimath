# Commutative rings in complete metric spaces

```agda
module analysis.commutative-rings-in-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
```

</details>

## Idea

A commutative ring in a complete metric space is a setting in which power series
and their convergence can be considered.

## Definition

```agda
Commutative-Ring-In-Complete-Metric-Space :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Commutative-Ring-In-Complete-Metric-Space l1 l2 =
  Σ ( Commutative-Ring l1)
    ( λ R →
      Σ ( Premetric l2 (type-Commutative-Ring R))
        ( λ μ →
          Σ ( is-metric-Premetric μ)
            ( λ is-metric-μ →
              is-complete-Metric-Space
                ( (type-Commutative-Ring R , μ) , is-metric-μ))))

module _
  {l1 l2 : Level} (RM : Commutative-Ring-In-Complete-Metric-Space l1 l2)
  where

  commutative-ring-Commutative-Ring-In-Complete-Metric-Space :
    Commutative-Ring l1
  commutative-ring-Commutative-Ring-In-Complete-Metric-Space = pr1 RM

  type-Commutative-Ring-In-Complete-Metric-Space : UU l1
  type-Commutative-Ring-In-Complete-Metric-Space =
    type-Commutative-Ring
      ( commutative-ring-Commutative-Ring-In-Complete-Metric-Space)

  structure-Commutative-Ring-In-Complete-Metric-Space :
    Premetric l2 type-Commutative-Ring-In-Complete-Metric-Space
  structure-Commutative-Ring-In-Complete-Metric-Space = pr1 (pr2 RM)

  is-metric-structure-Commutative-Ring-In-Complete-Metric-Space :
    is-metric-Premetric structure-Commutative-Ring-In-Complete-Metric-Space
  is-metric-structure-Commutative-Ring-In-Complete-Metric-Space =
    pr1 (pr2 (pr2 RM))

  metric-space-Commutative-Ring-In-Complete-Metric-Space : Metric-Space l1 l2
  metric-space-Commutative-Ring-In-Complete-Metric-Space =
    ( ( type-Commutative-Ring-In-Complete-Metric-Space ,
        structure-Commutative-Ring-In-Complete-Metric-Space) ,
      is-metric-structure-Commutative-Ring-In-Complete-Metric-Space)

  is-complete-metric-space-Commutative-Ring-In-Complete-Metric-Space :
    is-complete-Metric-Space
      metric-space-Commutative-Ring-In-Complete-Metric-Space
  is-complete-metric-space-Commutative-Ring-In-Complete-Metric-Space =
    pr2 (pr2 (pr2 RM))

  complete-metric-space-Commutative-Ring-In-Complete-Metric-Space :
    Complete-Metric-Space l1 l2
  complete-metric-space-Commutative-Ring-In-Complete-Metric-Space =
    ( metric-space-Commutative-Ring-In-Complete-Metric-Space ,
      is-complete-metric-space-Commutative-Ring-In-Complete-Metric-Space)
```

### Construction

```agda
commutative-ring-in-complete-metric-space-Commutative-Ring-Complete-Metric-Space :
  {l1 l2 : Level} →
  (R : Commutative-Ring l1) (M : Complete-Metric-Space l1 l2) →
  (type-Commutative-Ring R ＝ type-Complete-Metric-Space M) →
  Commutative-Ring-In-Complete-Metric-Space l1 l2
commutative-ring-in-complete-metric-space-Commutative-Ring-Complete-Metric-Space
  R M refl =
    ( R ,
      structure-Complete-Metric-Space M ,
      is-metric-structure-Complete-Metric-Space M ,
      is-complete-metric-space-Complete-Metric-Space M)
```
