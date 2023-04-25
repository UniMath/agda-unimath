# Product of Cauchy series of species of types in a subuniverse

```agda
module species.product-cauchy-series-species-of-types-in-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.cartesian-product-types
open import foundation.universe-levels
open import foundation.equivalences
open import foundation.homotopies
open import foundation.univalence
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types

open import species.species-of-types-in-subuniverse
open import species.cauchy-series-species-of-types
open import species.cauchy-series-species-of-types-in-subuniverse
open import species.cauchy-product-species-of-types
open import species.cauchy-product-species-of-types-in-subuniverse
open import species.product-cauchy-series-species-of-types
```

## Idea

The product of two Cauchy series is just the pointwise product.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  product-cauchy-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  product-cauchy-series-species-subuniverse =
    cauchy-series-species-subuniverse P (subuniverse-global-subuniverse Q l3) S X ×
    cauchy-series-species-subuniverse P (subuniverse-global-subuniverse Q l4) T X
```

## Property

### Equivalent with species of types

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-product-cauchy-series-Σ-extension-species-subuniverse :
    ( product-cauchy-series-species-types
       ( Σ-extension-species-subuniverse
           ( P)
           ( subuniverse-global-subuniverse Q l3)
           ( S))
       ( Σ-extension-species-subuniverse
           ( P)
           ( subuniverse-global-subuniverse Q l4)
           ( T))
       X)
      ≃
    product-cauchy-series-species-subuniverse P Q S T X
  equiv-product-cauchy-series-Σ-extension-species-subuniverse =
    equiv-prod
          ( inv-equiv
            ( equiv-cauchy-series-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l3)
                ( S)
                ( X)))
          ( inv-equiv
            ( equiv-cauchy-series-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l4)
                ( T)
                ( X)))
```

### The Cauchy series associated to the Cauchy product of `S` and `T` is equal to the product of theirs Cauchy series

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 :
    ( {l5 l6 : Level}
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l5 ⊔ l6))
        ( cauchy-product-species-subuniverse' P Q S T X)))
  (C2 :
    ( A B : UU l1) →
    is-in-subuniverse P A →
    is-in-subuniverse P B →
    is-in-subuniverse P (A + B))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-cauchy-series-cauchy-product-species-subuniverse :
    cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( X) ≃
    product-cauchy-series-species-subuniverse P Q S T X
  equiv-cauchy-series-cauchy-product-species-subuniverse =
    ( ( equiv-product-cauchy-series-Σ-extension-species-subuniverse P Q S T X) ∘e
      ( ( equiv-cauchy-series-cauchy-product-species-types
            ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l3)
                ( S))
            ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l4)
                ( T))
            ( X)) ∘e
        ( ( equiv-cauchy-series-equiv-species-types
              ( λ z →
                Σ-extension-species-subuniverse
                  ( P)
                  ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
                  ( cauchy-product-species-subuniverse P Q C1 S T) z)
              ( λ z →
                cauchy-product-species-types
                  ( Σ-extension-species-subuniverse
                      ( P)
                      ( subuniverse-global-subuniverse Q l3)
                      ( S))
                  ( Σ-extension-species-subuniverse
                      ( P)
                      ( subuniverse-global-subuniverse Q l4)
                      ( T))
                  z)
              ( equiv-cauchy-product-Σ-extension-species-subuniverse P Q C1 C2 S T)
              ( X)) ∘e
          ( ( equiv-cauchy-series-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
                ( cauchy-product-species-subuniverse P Q C1 S T)
                ( X))))))
```
