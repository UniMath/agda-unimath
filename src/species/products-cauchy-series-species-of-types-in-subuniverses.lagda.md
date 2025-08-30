# Products of Cauchy series of species of types in subuniverses

```agda
module species.products-cauchy-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.global-subuniverses
open import foundation.subuniverses
open import foundation.universe-levels

open import species.cauchy-products-species-of-types
open import species.cauchy-products-species-of-types-in-subuniverses
open import species.cauchy-series-species-of-types
open import species.cauchy-series-species-of-types-in-subuniverses
open import species.products-cauchy-series-species-of-types
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of Caucy series of species of types in subuniverses" Agda=product-cauchy-series-species-subuniverse}}
of two
[Cauchy series](species.cauchy-series-species-of-types-in-subuniverses.md) of
[species of types in subuniverses](species.species-of-types-in-subuniverses.md)
is just the pointwise [product](foundation.cartesian-product-types.md).

## Definition

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
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
  {α : Level → Level} {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
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
    inv-equiv
      ( equiv-product
        ( equiv-cauchy-series-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S)
          ( X))
        ( equiv-cauchy-series-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l4)
          ( T)
          ( X)))
```

### The Cauchy series associated to the Cauchy product of `S` and `T` is equal to the product of theirs Cauchy series

```agda
module _
  {α : Level → Level} {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
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
    ( equiv-product-cauchy-series-Σ-extension-species-subuniverse P Q S T X) ∘e
    ( equiv-cauchy-series-cauchy-product-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( X)) ∘e
    ( equiv-cauchy-series-equiv-species-types
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
    ( equiv-cauchy-series-Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( X))
```
