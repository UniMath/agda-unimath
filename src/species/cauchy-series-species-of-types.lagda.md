# Cauchy series of species of types

```agda
module species.cauchy-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types

open import species.species-of-types
```

</details>

## Idea

In classical mathematics, the Cauchy series of a species (of finite types) `S`
is the formal series in `x` :

```md
Σ (n : ℕ) (|S({1,...,n}| x^n / n!))
```

The categorified version of this series is :

```md
Σ (F : 𝔽) (S(F) × (F → X))
```

Remarks that we can generalized this to species of types with the following
definition :

```md
Σ (U : UU) (S(U) × (U → X))
```

## Definition

```agda
cauchy-series-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → UU l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
cauchy-series-species-types {l1} S X =
  Σ (UU l1) (λ U → S U × (U → X))
```

## Property

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (f : (F : UU l1) → (S F ≃ T F))
  (X : UU l4)
  where

  equiv-cauchy-series-equiv-species-types :
    cauchy-series-species-types S X ≃ cauchy-series-species-types T X
  equiv-cauchy-series-equiv-species-types =
    equiv-tot λ X → equiv-prod (f X) id-equiv

```
