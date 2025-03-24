# Composition of Cauchy series of species of types in subuniverses

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.composition-cauchy-series-species-of-types-in-subuniverses
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences funext
open import foundation.global-subuniverses funext univalence
open import foundation.sigma-closed-subuniverses funext univalence
open import foundation.subuniverses funext univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types funext univalence
open import species.cauchy-composition-species-of-types-in-subuniverses funext univalence
open import species.cauchy-series-species-of-types funext univalence
open import species.cauchy-series-species-of-types-in-subuniverses funext univalence
open import species.composition-cauchy-series-species-of-types funext univalence
open import species.species-of-types-in-subuniverses funext univalence
```

</details>

## Idea

The composition of Cauchy series of two species of subuniverse `S` and `T` at
`X` is defined as the Cauchy series of `S` applied to the Cauchy series of `T`
at `X`

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
  (Q : global-subuniverse (λ l → l))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l5)
  where

  equiv-composition-cauchy-series-Σ-extension-species-subuniverse :
    composition-cauchy-series-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( X) ≃
    composition-cauchy-series-species-subuniverse P Q S T X
  equiv-composition-cauchy-series-Σ-extension-species-subuniverse =
    ( inv-equiv
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
          ( S))
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
            ( X))))
```

### The Cauchy series associated to the composition of the species `S` and `T` is the composition of their Cauchy series

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C2 : is-closed-under-Σ-subuniverse P)
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
    ( equiv-composition-cauchy-series-Σ-extension-species-subuniverse P Q S T
      ( X)) ∘e
    ( ( equiv-cauchy-series-composition-species-types
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
          ( preserves-cauchy-composition-Σ-extension-species-subuniverse
            ( P)
            ( Q)
            ( C1)
            ( C2)
            ( S)
            ( T))
          ( X)) ∘e
        ( equiv-cauchy-series-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
          ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
          ( X))))
```
