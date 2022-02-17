# Decidability of dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.decidable-dependent-pair-types where

open import foundation.decidable-dependent-pair-types public

open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; contradiction-leq-ℕ; is-decidable-leq-ℕ; le-ℕ; is-decidable-le-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using (Fin)
open import elementary-number-theory.upper-bounds-natural-numbers using
  ( is-upper-bound-ℕ; is-strict-upper-bound-ℕ;
    is-upper-bound-is-strict-upper-bound-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-fam; is-decidable-prod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; ex-falso)
open import foundation.functions using (_∘_; id)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We describe conditions under which dependent sums are decidable.

```agda
is-decidable-Σ-ℕ :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ m x) × (P x))) → is-decidable (Σ ℕ P)
is-decidable-Σ-ℕ m P d (inl (pair x (pair l p))) = inl (pair x p)
is-decidable-Σ-ℕ zero-ℕ P d (inr f) =
  inr (λ p → f (pair (pr1 p) (pair star (pr2 p))))
is-decidable-Σ-ℕ (succ-ℕ m) P d (inr f) with d zero-ℕ
... | inl p = inl (pair zero-ℕ p)
... | inr g with
  is-decidable-Σ-ℕ m
    ( P ∘ succ-ℕ)
    ( λ x → d (succ-ℕ x))
    ( inr (λ p → f (pair (succ-ℕ (pr1 p)) (pr2 p))))
... | inl p = inl (pair (succ-ℕ (pr1 p)) (pr2 p))
... | inr h = inr α
  where
  α : Σ ℕ P → empty
  α (pair zero-ℕ p) = g p
  α (pair (succ-ℕ x) p) = h (pair x p)

is-decidable-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-upper-bound-ℕ P m) → is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-Σ-ℕ
    ( succ-ℕ m)
    ( λ x → (P x) × (Q x))
    ( λ x → is-decidable-prod (dP x) (dQ x))
    ( inr
      ( λ p →
        contradiction-leq-ℕ
          ( pr1 p)
          ( m)
          ( H (pr1 p) (pr1 (pr2 (pr2 p))))
          ( pr1 (pr2 p))))

is-decidable-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ x m) × (P x)))
is-decidable-bounded-Σ-ℕ' m P d =
  is-decidable-bounded-Σ-ℕ m
    ( λ x → leq-ℕ x m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( λ x → id)

is-decidable-strictly-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-strict-upper-bound-ℕ P m) →
  is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-strictly-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-bounded-Σ-ℕ m P Q dP dQ
    ( is-upper-bound-is-strict-upper-bound-ℕ P m H)

is-decidable-strictly-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (le-ℕ x m) × (P x)))
is-decidable-strictly-bounded-Σ-ℕ' m P d =
  is-decidable-strictly-bounded-Σ-ℕ m
    ( λ x → le-ℕ x m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( λ x → id)
```

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
