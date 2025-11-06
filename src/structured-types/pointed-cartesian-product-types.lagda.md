# Pointed cartesian product types

```agda
module structured-types.pointed-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `a : A` and
`b : B`, their [cartesian product](foundation.cartesian-product-types.md) is
again canonically pointed at `(a , b) : A × B`. We call this the
{{#concept "pointed cartesian product" Agda=product-Pointed-Type}} or **pointed
product** of the two pointed types.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  product-Pointed-Type :
    (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
  product-Pointed-Type (A , a) (B , b) = (A × B , (a , b))

  infixr 15 _×∗_
  _×∗_ = product-Pointed-Type
```

## Properties

### The pointed projections from the pointed product `A ×∗ B` onto `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-pr1-product-Pointed-Type :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type A
  map-pr1-product-Pointed-Type = pr1

  pr1-product-Pointed-Type : (A ×∗ B) →∗ A
  pr1 pr1-product-Pointed-Type = map-pr1-product-Pointed-Type
  pr2 pr1-product-Pointed-Type = refl

  map-pr2-product-Pointed-Type :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type B
  map-pr2-product-Pointed-Type = pr2

  pr2-product-Pointed-Type : (A ×∗ B) →∗ B
  pr1 pr2-product-Pointed-Type = map-pr2-product-Pointed-Type
  pr2 pr2-product-Pointed-Type = refl
```

### The pointed product `A ×∗ B` comes equipped with pointed inclusion of `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-inl-product-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type (A ×∗ B)
  pr1 (map-inl-product-Pointed-Type x) = x
  pr2 (map-inl-product-Pointed-Type x) = point-Pointed-Type B

  inl-product-Pointed-Type : A →∗ (A ×∗ B)
  pr1 inl-product-Pointed-Type = map-inl-product-Pointed-Type
  pr2 inl-product-Pointed-Type = refl

  map-inr-product-Pointed-Type :
    type-Pointed-Type B → type-Pointed-Type (A ×∗ B)
  pr1 (map-inr-product-Pointed-Type y) = point-Pointed-Type A
  pr2 (map-inr-product-Pointed-Type y) = y

  inr-product-Pointed-Type : B →∗ (A ×∗ B)
  pr1 inr-product-Pointed-Type = map-inr-product-Pointed-Type
  pr2 inr-product-Pointed-Type = refl
```

### The pointed inclusions into `A ×∗ B` are sections to the pointed projections

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  is-section-map-inl-product-Pointed-Type :
    (map-pr1-product-Pointed-Type A B ∘ map-inl-product-Pointed-Type A B) ~ id
  is-section-map-inl-product-Pointed-Type = refl-htpy

  is-section-map-inr-product-Pointed-Type :
    (map-pr2-product-Pointed-Type A B ∘ map-inr-product-Pointed-Type A B) ~ id
  is-section-map-inr-product-Pointed-Type = refl-htpy
```

### The pointed gap map for the pointed product

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-gap-product-Pointed-Type :
    {l3 : Level} {S : Pointed-Type l3}
    (f : S →∗ A) (g : S →∗ B) →
    type-Pointed-Type S → type-Pointed-Type (A ×∗ B)
  pr1 (map-gap-product-Pointed-Type f g x) = map-pointed-map f x
  pr2 (map-gap-product-Pointed-Type f g x) = map-pointed-map g x

  gap-product-Pointed-Type :
    {l3 : Level} {S : Pointed-Type l3}
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ×∗ B)
  pr1 (gap-product-Pointed-Type f g) =
    map-gap-product-Pointed-Type f g
  pr2 (gap-product-Pointed-Type f g) =
    eq-pair
      ( preserves-point-pointed-map f)
      ( preserves-point-pointed-map g)
```
