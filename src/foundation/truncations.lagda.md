# Truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncations where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; is-equiv; map-inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_)
open import foundation.truncated-types using
  ( is-trunc; Truncated-Type; type-Truncated-Type)
open import foundation-core.truncation-levels using (𝕋)
open import foundation.universal-property-truncation using
  ( is-truncation; precomp-Trunc; universal-property-truncation;
    universal-property-truncation-is-truncation; map-is-truncation;
    triangle-is-truncation; precomp-Π-Truncated-Type;
    dependent-universal-property-truncation-is-truncation;
    dependent-universal-property-truncation)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We postulate the existence of truncations

## Postulates

```agda
postulate
  type-trunc : {l : Level} (k : 𝕋) → UU l → UU l

postulate
  is-trunc-type-trunc :
    {l : Level} {k : 𝕋} {A : UU l} → is-trunc k (type-trunc k A)

trunc : {l : Level} (k : 𝕋) → UU l → Truncated-Type l k
pr1 (trunc k A) = type-trunc k A
pr2 (trunc k A) = is-trunc-type-trunc

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
    is-truncation l2 (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  (type-trunc k A → type-Truncated-Type B) ≃ (A → type-Truncated-Type B)
pr1 (equiv-universal-property-trunc A B) = precomp-Trunc unit-trunc B
pr2 (equiv-universal-property-trunc A B) = is-truncation-trunc B
```

## Properties

### The n-truncations satisfy the universal property

```agda
universal-property-trunc :
  {l1 : Level} (k : 𝕋) (A : UU l1) →
  {l2 : Level} → universal-property-truncation l2 (trunc k A) unit-trunc
universal-property-trunc k A =
  universal-property-truncation-is-truncation
    ( trunc k A)
    ( unit-trunc)
    ( is-truncation-trunc)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  where
  
  map-universal-property-trunc :
    (B : Truncated-Type l2 k) → (A → type-Truncated-Type B) →
    type-trunc k A → type-Truncated-Type B
  map-universal-property-trunc =
    map-is-truncation (trunc k A) unit-trunc is-truncation-trunc

  triangle-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    (map-universal-property-trunc B f ∘ unit-trunc) ~ f
  triangle-universal-property-trunc =
    triangle-is-truncation (trunc k A) unit-trunc is-truncation-trunc

  apply-universal-property-trunc :
    (x : type-trunc k A) (B : Truncated-Type l2 k) →
    (A → type-Truncated-Type B) → type-Truncated-Type B
  apply-universal-property-trunc x B f =
    map-universal-property-trunc B f x
```

### The n-truncations satisfy the dependent universal property

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  dependent-universal-property-trunc :
    {l : Level} →
    dependent-universal-property-truncation l (trunc k A) unit-trunc
  dependent-universal-property-trunc =
    dependent-universal-property-truncation-is-truncation
      ( trunc k A)
      ( unit-trunc)
      ( is-truncation-trunc)

  equiv-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : type-trunc k A) → type-Truncated-Type (B x)) ≃
    ((a : A) → type-Truncated-Type (B (unit-trunc a)))
  pr1 (equiv-dependent-universal-property-trunc B) =
    precomp-Π-Truncated-Type unit-trunc B
  pr2 (equiv-dependent-universal-property-trunc B) =
    dependent-universal-property-trunc B

  apply-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : A) → type-Truncated-Type (B (unit-trunc x))) →
    (x : type-trunc k A) → type-Truncated-Type (B x)
  apply-dependent-universal-property-trunc B =
    map-inv-equiv (equiv-dependent-universal-property-trunc B)
```
