# Universal property of contractible types with respect to pointed types and maps

```agda
module structured-types.pointed-universal-property-contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-contractible-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

By definition, a [contractible](foundation-core.contractible-types.md) type is
[pointed](structured-types.pointed-types.md). Moreover, they enjoy a
{{#concept "universal property" Disambiguation="of contractible pointed types" Agda=universal-property-contr-Pointed-Type}}
among the pointed types with respect to
[pointed maps](structured-types.pointed-maps.md):

A pointed type `A` is contractible if for all pointed types `X`, the type of
pointed maps `A →∗ X` is contractible.

## Definitions

### The universal property of contractible types with respect to pointed types and maps

```agda
module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  universal-property-contr-Pointed-Type : UUω
  universal-property-contr-Pointed-Type =
    {l : Level} (X : Pointed-Type l) → is-contr (A →∗ X)
```

## Properties

### A contractible type has the universal property of contractible types with respect to pointed types and maps

**Proof:** If `A` is contractible with a point `a : A`, then we have

```text
   ((A , a) →∗ (X , x))
 ≃ Σ (A → X) (λ f → f a ＝ x)
 ≃ Σ X (λ y → y ＝ x)
```

where the last equivalence holds since `(A → X) ≃ X` by the
[universal property of contractible types](foundation.universal-property-contractible-types.md).

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  universal-property-contr-is-contr-Pointed-Type' :
    is-contr A → universal-property-contr-Pointed-Type (A , a)
  universal-property-contr-is-contr-Pointed-Type' c (X , x) =
    is-contr-equiv
      ( Σ X (λ y → y ＝ x))
      ( equiv-Σ-equiv-base _ (equiv-universal-property-contr a c X))
      ( is-torsorial-Id' x)

module _
  {l1 : Level} {A : UU l1}
  where

  universal-property-contr-is-contr-Pointed-Type :
    (c : is-contr A) → universal-property-contr-Pointed-Type (A , center c)
  universal-property-contr-is-contr-Pointed-Type c =
    universal-property-contr-is-contr-Pointed-Type' (center c) c
```

### A pointed type with the universal property of contractible types with respect to pointed types and maps is contractible

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-contr-universal-property-contr-Pointed-Type' :
    universal-property-contr-Pointed-Type (A , a) → is-contr A
  is-contr-universal-property-contr-Pointed-Type' up =
    is-contr-universal-property-contr a
      ( λ X →
        is-equiv-htpy-equiv
          ( equivalence-reasoning
              (A → X)
              ≃ Σ (A → X) (λ f → Σ X (λ x → f a ＝ x))
                by inv-right-unit-law-Σ-is-contr (λ f → is-torsorial-Id (f a))
              ≃ Σ X (λ x → (A , a) →∗ (X , x))
                by equiv-left-swap-Σ
              ≃ X
                by equiv-pr1 (λ x → up (X , x)))
            ( λ f →
              ap
                ( pr1)
                ( inv
                  ( contraction (is-torsorial-Id (f a)) (pair (f a) refl)))))

module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  is-contr-universal-property-contr-Pointed-Type :
    universal-property-contr-Pointed-Type A → is-contr (type-Pointed-Type A)
  is-contr-universal-property-contr-Pointed-Type =
    is-contr-universal-property-contr-Pointed-Type' (point-Pointed-Type A)
```
