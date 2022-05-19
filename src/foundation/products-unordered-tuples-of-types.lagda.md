---
title: Products of unordered tuples of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.products-unordered-tuples-of-types where

open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.commutative-operations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels
open import foundation.unordered-tuples
open import foundation.unordered-tuples-of-types

open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.universal-property-standard-finite-types
```

## Idea

Given an unordered pair of types, we can take their product. This is a commutative version of the cartesian product operation on types.

## Definition

```agda
product-unordered-tuple-types :
  {l : Level} {n : ℕ} → unordered-tuple n (UU l) → (UU l)
product-unordered-tuple-types p =
  (x : type-unordered-tuple p) → element-unordered-tuple p x

pr-product-unordered-tuple-types :
  {l : Level} {n : ℕ} (A : unordered-tuple-types l n)
  (i : type-unordered-tuple A) →
  product-unordered-tuple-types A → element-unordered-tuple A i
pr-product-unordered-tuple-types A i f = f i

equiv-pr-product-unordered-tuple-types :
  {l : Level} {n : ℕ} (A : unordered-tuple-types l (succ-ℕ n))
  (i : type-unordered-tuple A) →
  ( ( product-unordered-tuple-types
      ( unordered-tuple-complement-point-type-unordered-tuple A i)) ×
    ( element-unordered-tuple A i)) ≃
  product-unordered-tuple-types A
equiv-pr-product-unordered-tuple-types A i =
  ( equiv-Π
    ( element-unordered-tuple A)
    ( equiv-maybe-structure-point-UU-Fin (type-unordered-tuple-UU-Fin A) i)
    ( λ x → id-equiv)) ∘e
  ( inv-equiv
    ( equiv-dependent-universal-property-Maybe
      ( λ j →
        element-unordered-tuple A
          ( map-equiv (equiv-maybe-structure-point-UU-Fin
            ( type-unordered-tuple-UU-Fin A) i)
            ( j)))))

map-equiv-pr-product-unordered-tuple-types :
  {l : Level} {n : ℕ} (A : unordered-tuple-types l (succ-ℕ n))
  (i : type-unordered-tuple A) →
  product-unordered-tuple-types
    ( unordered-tuple-complement-point-type-unordered-tuple A i) →
  element-unordered-tuple A i → product-unordered-tuple-types A
map-equiv-pr-product-unordered-tuple-types A i f a =
  map-equiv (equiv-pr-product-unordered-tuple-types A i) (pair f a)
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1 l2 : Level} {n : ℕ} (A : unordered-tuple-types l1 n)
  (B : unordered-tuple-types l2 n)
  where

  equiv-product-unordered-tuple-types :
    equiv-unordered-tuple-types A B →
    product-unordered-tuple-types A ≃ product-unordered-tuple-types B
  equiv-product-unordered-tuple-types e =
    equiv-Π
      ( element-unordered-tuple B)
      ( equiv-type-equiv-unordered-tuple-types A B e)
      ( equiv-element-equiv-unordered-tuple-types A B e)
```
