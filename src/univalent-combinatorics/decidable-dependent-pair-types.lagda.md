---
title: Decidability of dependent pair types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.decidable-dependent-pair-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-dependent-pair-types using
  ( is-decidable-Σ-equiv)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.functions using (_∘_)
open import foundation.equivalences using (id-equiv)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; equiv-count; map-equiv-count)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We describe conditions under which dependent sums are decidable. Note that it is _not_ the case for a family `B` of decidable types over a finite type `A`, that the dependent pair type `Σ A B` is decidable.

## Properties

### The Σ-type of any family of decidable types over `Fin k` is decidable

```agda
is-decidable-Σ-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
is-decidable-Σ-Fin {l} {zero-ℕ} {P} d = inr pr1
is-decidable-Σ-Fin {l} {succ-ℕ k} {P} d with d (inr star)
... | inl p = inl (pair (inr star) p)
... | inr f =
  is-decidable-iff
    ( λ t → pair (inl (pr1 t)) (pr2 t))
    ( g)
    ( is-decidable-Σ-Fin {l} {k} {P ∘ inl} (λ x → d (inl x)))
  where
  g : Σ (Fin (succ-ℕ k)) P → Σ (Fin k) (P ∘ inl)
  g (pair (inl x) p) = pair x p
  g (pair (inr star) p) = ex-falso (f p)
```

### The Σ-type of any family of decidable types over a type equipped with count is decidable

```agda
is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))
```
