---
title: The image of a map
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.image-of-maps where

open import foundation.images public

open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using (is-decidable-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.fibers-of-maps using (equiv-total-fib; fib)
open import foundation.propositional-truncations using (trunc-Prop)
open import foundation.subtypes using
  ( extensionality-type-subtype')
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.equality-finite-types using
  ( is-finite-eq)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-equiv')
open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-base-is-finite-Σ-merely-inhabited; is-finite-Σ)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  abstract
    is-finite-codomain :
      is-surjective f → has-decidable-equality B → is-finite B
    is-finite-codomain H d =
      is-finite-base-is-finite-Σ-merely-inhabited
        ( is-set-has-decidable-equality d)
        ( H)
        ( is-finite-equiv' (equiv-total-fib f) K)
        ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

abstract
  is-finite-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
    has-decidable-equality B → is-finite (im f)
  is-finite-im {f = f} K d =
    is-finite-codomain K
      ( is-surjective-map-unit-im f)
      ( λ x y →
        is-decidable-equiv
          ( extensionality-type-subtype' (λ u → trunc-Prop (fib f u)) x y)
          ( d (pr1 x) (pr1 y)))
```
