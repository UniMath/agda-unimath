---
title: Combinatorial identities of sums of natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.sums-of-natural-numbers where


open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.sums-of-natural-numbers public

open import foundation.dependent-pair-types using (ind-Σ)
open import foundation.identity-types using (Id; inv; _∙_)
open import foundation.type-arithmetic-dependent-pair-types using
  ( inv-assoc-Σ)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using (count; count-Fin)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-Σ; number-of-elements-count-Σ)
open import univalent-combinatorics.double-counting using
  ( double-counting-equiv)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We use counting methods to prove identities of sums of natural numbers

### Finite sums are associative

```agda
abstract
  associative-sum-count-ℕ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
    Id ( sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)))
       ( sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f))
  associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
    ( ( htpy-sum-count-ℕ count-A
        ( λ x →
          inv
          ( number-of-elements-count-Σ
            ( count-B x)
            ( λ y → count-Fin (f x y))))) ∙
      ( inv
        ( number-of-elements-count-Σ count-A
          ( λ x → count-Σ (count-B x) (λ y → count-Fin (f x y)))))) ∙
    ( ( double-counting-equiv
        ( count-Σ count-A (λ x → count-Σ (count-B x) (λ y → count-Fin (f x y))))
        ( count-Σ (count-Σ count-A count-B) (λ x → count-Fin (ind-Σ f x)))
        ( inv-assoc-Σ A B (λ x → Fin (ind-Σ f x)))) ∙
      ( number-of-elements-count-Σ
        ( count-Σ count-A count-B)
        ( λ x → (count-Fin (ind-Σ f x)))))
```
