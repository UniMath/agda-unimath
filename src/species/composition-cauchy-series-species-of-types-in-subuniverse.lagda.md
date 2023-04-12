# Composition of Cauchy series of species of types in subuniverse

```agda
module species.composition-cauchy-series-species-of-types-in-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-cartesian-product-types
open import foundation.cartesian-product-types
open import foundation.universe-levels
open import foundation.equivalences
open import foundation.homotopies
open import foundation.univalence
open import foundation.functions
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice

open import species.composition-cauchy-series-species-of-types
open import species.cauchy-composition-species-of-types
open import species.cauchy-composition-species-of-types-in-subuniverse
open import species.species-of-types-in-subuniverse
open import species.cauchy-series-species-of-types
open import species.cauchy-series-species-of-types-in-subuniverse
```

## Idea

The composition of Cauchy series of two species of subuniverse `S` and `T` at
`X` is defined as the Cauchy series of `S` applied to the Cauchy series of `T`
at `X`

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

  composition-cauchy-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  composition-cauchy-series-species-subuniverse =
    cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l3)
      ( S)
      ( cauchy-series-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l4)
          ( T)
          ( X))
```

## Property

### Equivalent form with species of types

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-composition-cauchy-series-Σ-extension-species-subuniverse :
    ( composition-cauchy-series-species-types
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
    composition-cauchy-series-species-subuniverse P Q S T X
  equiv-composition-cauchy-series-Σ-extension-species-subuniverse =
    ( ( inv-equiv
          ( equiv-cauchy-series-Σ-extension-species-subuniverse
              ( P)
              ( subuniverse-global-subuniverse Q l3)
              ( S)
              ( cauchy-series-species-subuniverse
                 ( P)
                 ( subuniverse-global-subuniverse Q l4)
                 ( T)
                 ( X)))) ∘e
      ( equiv-cauchy-series-species-types
          ( Σ-extension-species-subuniverse
              ( P)
              ( subuniverse-global-subuniverse Q l3)
              ( S) )
          ( cauchy-series-species-types
              ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l4)
                ( T))
              ( X))
          ( cauchy-series-species-subuniverse
              ( P)
              ( subuniverse-global-subuniverse Q l4)
              ( T)
              ( X))
          ( inv-equiv
              ( equiv-cauchy-series-Σ-extension-species-subuniverse
                  ( P)
                  ( subuniverse-global-subuniverse Q l4)
                  ( T)
                  ( X)))))
```

### The Cauchy series associated to the composition of the species `S` and `T` is the composition of their Cauchy series

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 :
    {l5 l6 : Level}
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
    (X : type-subuniverse P) →
    is-in-subuniverse
      (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l5 ⊔ l6))
      (cauchy-composition-species-subuniverse' P Q S T X))
  (C2 :
    ( ( X : type-subuniverse P) →
      ( Y : (inclusion-subuniverse P X) → type-subuniverse P) →
      is-in-subuniverse P
        ( Σ (inclusion-subuniverse P X) (λ x → inclusion-subuniverse P (Y x)))))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-cauchy-series-composition-species-subuniverse :
    cauchy-series-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
      ( X) ≃
    composition-cauchy-series-species-subuniverse P Q S T X
  equiv-cauchy-series-composition-species-subuniverse =
   ( ( equiv-composition-cauchy-series-Σ-extension-species-subuniverse
         P
         Q
         S
         T
         X) ∘e
     ( ( equiv-cauchy-series-composition-species-types
           ( Σ-extension-species-subuniverse
               ( P)
               ( subuniverse-global-subuniverse Q l3)
               ( S))
           ( Σ-extension-species-subuniverse
               ( P)
               ( subuniverse-global-subuniverse Q l4)
               ( T))
           ( X) ) ∘e
       ( ( equiv-cauchy-series-equiv-species-types
             ( Σ-extension-species-subuniverse
                 ( P)
                 ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
                 ( cauchy-composition-species-subuniverse P Q C1 C2 S T))
             ( cauchy-composition-species-types
                 ( Σ-extension-species-subuniverse
                     ( P)
                     ( subuniverse-global-subuniverse Q l3)
                     ( S))
                 ( Σ-extension-species-subuniverse
                     ( P)
                     ( subuniverse-global-subuniverse Q l4)
                     ( T)))
             ( equiv-cauchy-composition-Σ-extension-species-subuniverse
                 ( P)
                 ( Q)
                 ( C1)
                 ( C2)
                 ( S)
                 ( T) )
             ( X)) ∘e
         ( equiv-cauchy-series-Σ-extension-species-subuniverse
             ( P)
             ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
             ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
             ( X)))))
```
