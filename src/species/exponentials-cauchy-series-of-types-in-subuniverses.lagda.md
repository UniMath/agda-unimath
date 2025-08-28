# Exponential of Cauchy series of species of types in subuniverses

```agda
module species.exponentials-cauchy-series-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.sigma-closed-subuniverses
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types-in-subuniverses
open import species.cauchy-exponentials-species-of-types-in-subuniverses
open import species.cauchy-series-species-of-types-in-subuniverses
open import species.composition-cauchy-series-species-of-types-in-subuniverses
open import species.species-of-types-in-subuniverses
```

</details>

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  (X : UU l5)
  where

  exponential-cauchy-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l5)
  exponential-cauchy-series-species-subuniverse =
    Σ ( type-subuniverse P)
      ( λ F →
        inclusion-subuniverse P F →
        Σ ( type-subuniverse P)
          ( λ U →
            ( inclusion-subuniverse Q (S U)) ×
            ( inclusion-subuniverse P U → X)))
```

## Property

### The exponential of a Cauchy series as a composition

```agda
module _
  {l1 l2 l3 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C : is-in-subuniverse (subuniverse-global-subuniverse Q lzero) unit)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : UU l5)
  where

  equiv-exponential-cauchy-series-composition-unit-species-subuniverse :
    composition-cauchy-series-species-subuniverse P Q (λ _ → unit , C) S X ≃
    exponential-cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l3)
      ( S)
      ( X)
  equiv-exponential-cauchy-series-composition-unit-species-subuniverse =
    equiv-tot (λ F → left-unit-law-product)
```

### The Cauchy series associated to the Cauchy exponential of `S` is equal to the exponential of its Cauchy series

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-exponential-species-subuniverse P Q)
  (C2 : is-in-subuniverse (subuniverse-global-subuniverse Q lzero) unit)
  (C3 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C4 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : UU l4)
  where

  equiv-cauchy-series-cauchy-exponential-species-subuniverse :
    cauchy-series-species-subuniverse P
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-exponential-species-subuniverse P Q C1 S)
      ( X) ≃
    exponential-cauchy-series-species-subuniverse P
      ( subuniverse-global-subuniverse Q l3)
      ( S)
      ( X)
  equiv-cauchy-series-cauchy-exponential-species-subuniverse =
    ( equiv-exponential-cauchy-series-composition-unit-species-subuniverse
      ( P)
      ( Q)
      ( C2)
      ( S)
      ( X)) ∘e
    ( equiv-cauchy-series-composition-species-subuniverse P Q C3 C4
      ( λ _ → unit , C2)
      ( S)
      ( X)) ∘e
    ( equiv-cauchy-series-equiv-species-subuniverse P Q
      ( cauchy-exponential-species-subuniverse P Q C1 S)
      ( cauchy-composition-species-subuniverse P Q C3 C4
        ( λ _ → unit , C2)
        ( S))
      ( λ F →
        inv-equiv
          ( equiv-cauchy-exponential-composition-unit-species-subuniverse
            ( P)
            ( Q)
            ( C1)
            ( C2)
            ( C3)
            ( C4)
            ( S)
            ( F)))
      ( X))
```
