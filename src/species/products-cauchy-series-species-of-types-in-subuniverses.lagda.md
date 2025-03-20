# Products of Cauchy series of species of types in subuniverses

```agda
open import foundation.function-extensionality-axiom

module
  species.products-cauchy-series-species-of-types-in-subuniverses
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.coproduct-types funext
open import foundation.equivalences funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.global-subuniverses funext
open import foundation.subuniverses funext
open import foundation.universe-levels

open import species.cauchy-products-species-of-types funext
open import species.cauchy-products-species-of-types funext-in-subuniverses
open import species.cauchy-series-species-of-types funext
open import species.cauchy-series-species-of-types funext-in-subuniverses
open import species.products-cauchy-series-species-of-types funext
open import species.species-of-types-in-subuniverses funext
```

</details>

## Idea

The product of two Cauchy series is just the pointwise product.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  product-cauchy-series-species-subuniverse :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  product-cauchy-series-species-subuniverse =
    ( cauchy-series-species-subuniverse
      P (subuniverse-global-subuniverse Q l3) S X) ×
    ( cauchy-series-species-subuniverse
      P (subuniverse-global-subuniverse Q l4) T X)
```

## Properties

### Equivalent with species of types

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
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
    equiv-product
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
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-product-species-subuniverse P Q)
  (C2 : is-closed-under-coproducts-subuniverse P)
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
    ( equiv-product-cauchy-series-Σ-extension-species-subuniverse P Q S T X ∘e
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
              ( equiv-cauchy-product-Σ-extension-species-subuniverse
                  P Q C1 C2 S T)
              ( X)) ∘e
          ( ( equiv-cauchy-series-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
                ( cauchy-product-species-subuniverse P Q C1 S T)
                ( X))))))
```
