# Exponential of Cauchy series of species of types

```agda
module species.exponentials-cauchy-series-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.cauchy-exponentials-species-of-types
open import species.cauchy-series-species-of-types
open import species.composition-cauchy-series-species-of-types
open import species.species-of-types
```

</details>

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (X : UU l3)
  where

  exponential-cauchy-series-species-types :
    UU (lsuc l1 ⊔ l2 ⊔ l3)
  exponential-cauchy-series-species-types =
    Σ ( UU l1)
      ( λ F → (F → Σ (UU l1) (λ U → S U × (U → X))))
```

## Properties

### The exponential of a Cauchy series as a composition

```agda
  equiv-exponential-cauchy-series-composition-unit-species-types :
    composition-cauchy-series-species-types (λ _ → unit) S X ≃
    exponential-cauchy-series-species-types
  equiv-exponential-cauchy-series-composition-unit-species-types =
    equiv-tot (λ F → left-unit-law-product)
```

### The Cauchy series associated to the Cauchy exponential of `S` is equal to the exponential of its Cauchy series

```agda
  equiv-cauchy-series-cauchy-exponential-species-types :
    cauchy-series-species-types (cauchy-exponential-species-types S) X ≃
    exponential-cauchy-series-species-types
  equiv-cauchy-series-cauchy-exponential-species-types =
    ( equiv-exponential-cauchy-series-composition-unit-species-types) ∘e
    ( equiv-cauchy-series-composition-species-types (λ _ → unit) S X) ∘e
    ( equiv-cauchy-series-equiv-species-types
      ( cauchy-exponential-species-types S)
      ( cauchy-composition-species-types (λ _ → unit) S)
      ( λ F →
        inv-equiv (equiv-cauchy-exponential-composition-unit-species-types S F))
      ( X))
```
