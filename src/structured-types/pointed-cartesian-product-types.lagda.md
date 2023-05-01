# Pointed cartesian product types

```agda
module structured-types.pointed-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given two pointed types `a : A` and `b : B`, their cartesian product is again
canonically pointed at `(a , b) : A × B`. We call this the **pointed cartesian
product** or **pointed product** of the two pointed types.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  prod-Pointed-Type :
    (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
  pr1 (prod-Pointed-Type (A , a) (B , b)) = A × B
  pr2 (prod-Pointed-Type (A , a) (B , b)) = a , b

  _×*_ = prod-Pointed-Type
```

## Properties

### The pointed projections from the pointed product to `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-pr1-prod-Pointed-Type : type-Pointed-Type (A ×* B) → type-Pointed-Type A
  map-pr1-prod-Pointed-Type = pr1

  pr1-prod-Pointed-Type : (A ×* B) →* A
  pr1 pr1-prod-Pointed-Type = map-pr1-prod-Pointed-Type
  pr2 pr1-prod-Pointed-Type = refl

  map-pr2-prod-Pointed-Type : type-Pointed-Type (A ×* B) → type-Pointed-Type B
  map-pr2-prod-Pointed-Type = pr2

  pr2-prod-Pointed-Type : (A ×* B) →* B
  pr1 pr2-prod-Pointed-Type = map-pr2-prod-Pointed-Type
  pr2 pr2-prod-Pointed-Type = refl
```

### The pointed product comes equipped with pointed inclusion of `A` and `B`

```agda
  map-inl-prod-Pointed-Type : type-Pointed-Type A → type-Pointed-Type (A ×* B)
  pr1 (map-inl-prod-Pointed-Type x) = x
  pr2 (map-inl-prod-Pointed-Type x) = point-Pointed-Type B

  inl-prod-Pointed-Type : A →* (A ×* B)
  pr1 inl-prod-Pointed-Type = map-inl-prod-Pointed-Type
  pr2 inl-prod-Pointed-Type = refl

  map-inr-prod-Pointed-Type : type-Pointed-Type B → type-Pointed-Type (A ×* B)
  pr1 (map-inr-prod-Pointed-Type y) = point-Pointed-Type A
  pr2 (map-inr-prod-Pointed-Type y) = y

  inr-prod-Pointed-Type : B →* (A ×* B)
  pr1 inr-prod-Pointed-Type = map-inr-prod-Pointed-Type
  pr2 inr-prod-Pointed-Type = refl
```

### The pointed inclusions are sections to the pointed projections

```agda
  issec-map-inl-prod-Pointed-Type :
    (map-pr1-prod-Pointed-Type ∘ map-inl-prod-Pointed-Type) ~ id
  issec-map-inl-prod-Pointed-Type = refl-htpy

  issec-map-inr-prod-Pointed-Type :
    (map-pr2-prod-Pointed-Type ∘ map-inr-prod-Pointed-Type) ~ id
  issec-map-inr-prod-Pointed-Type = refl-htpy
```
