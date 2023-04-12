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

open import species.large-composition-species-of-types
open import species.species-of-types-in-subuniverse
open import species.cauchy-series-species-of-types
open import species.cauchy-series-species-of-types-in-subuniverse
open import species.cauchy-product-species-of-types
```

## Idea

The composition of Cauchy series of two species of subuniverse `S` and `T` at `X` is
defined as the Cauchy series of `S` applied to the Cauchy series of `T` at `X`

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
