# Truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncations where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_)
open import foundation.truncated-types using
  ( is-trunc; UU-Truncated-Type; type-Truncated-Type)
open import foundation.truncation-levels using (𝕋)
open import foundation.universal-property-truncation using
  ( is-truncation; precomp-Trunc; universal-property-truncation;
    universal-property-truncation-is-truncation; map-is-truncation;
    triangle-is-truncation)
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

trunc : {l : Level} (k : 𝕋) → UU l → UU-Truncated-Type l k
pr1 (trunc k A) = type-trunc k A
pr2 (trunc k A) = is-trunc-type-trunc

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
    is-truncation l2 (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : UU-Truncated-Type l2 k) →
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

map-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : UU-Truncated-Type l2 k) →
  (A → type-Truncated-Type B) → type-trunc k A → type-Truncated-Type B
map-universal-property-trunc {k = k} {A} =
  map-is-truncation
    ( trunc k A)
    ( unit-trunc)
    ( is-truncation-trunc)

triangle-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : UU-Truncated-Type l2 k) →
  (f : A → type-Truncated-Type B) →
  (map-universal-property-trunc B f ∘ unit-trunc) ~ f
triangle-universal-property-trunc {k = k} {A} =
  triangle-is-truncation
    ( trunc k A)
    ( unit-trunc)
    ( is-truncation-trunc)
```

```agda
{-
apply-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : UU-Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set t B f =
  map-universal-property-trunc-Set B f t

abstract
  dependent-universal-property-trunc-Set :
    {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) → 
    is-equiv (precomp-Π-Set unit-trunc-Set B)
  dependent-universal-property-trunc-Set {A = A} =
    dependent-universal-property-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set B =
  pair ( precomp-Π-Set unit-trunc-Set B)
       ( dependent-universal-property-trunc-Set B)

apply-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1}
  (B : type-trunc-Set A → UU-Set l2) →
  ((x : A) → type-Set (B (unit-trunc-Set x))) →
  (x : type-trunc-Set A) → type-Set (B x)
apply-dependent-universal-property-trunc-Set B =
  map-inv-equiv (equiv-dependent-universal-property-trunc-Set B)
-}
```
