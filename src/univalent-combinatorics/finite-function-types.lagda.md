---
title: Finite function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-function-types where

open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.cartesian-product-types using
  ( is-finite-prod)
open import univalent-combinatorics.dependent-product-finite-types using
  ( is-finite-Π)
open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-Σ)
open import univalent-combinatorics.equality-finite-types using
  ( is-finite-eq; has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  ( is-finite; 𝔽; type-𝔽; is-finite-type-𝔽)
```

```agda
abstract
  is-finite-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A → B)
  is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A →-𝔽 B) = type-𝔽 A → type-𝔽 B
pr2 (A →-𝔽 B) =
  is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

abstract
  is-finite-≃ :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A ≃ B)
  is-finite-≃ f g =
    is-finite-Σ
      ( is-finite-function-type f g)
      ( λ h →
        is-finite-prod
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π g
                ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π f
                ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A ≃-𝔽 B) = type-𝔽 A ≃ type-𝔽 B
pr2 (A ≃-𝔽 B) = is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A
```
