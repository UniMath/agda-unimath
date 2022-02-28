# Decidable dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.decidable-dependent-function-types where

open import foundation.decidable-dependent-function-types public

open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; leq-zero-ℕ; contradiction-leq-ℕ; is-decidable-leq-ℕ; leq-le-ℕ; le-ℕ;
    is-decidable-le-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; ind-ℕ)
open import elementary-number-theory.upper-bounds-natural-numbers using
  ( is-upper-bound-ℕ; is-strict-upper-bound-ℕ)

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-function-type)
open import foundation.empty-types using (ind-empty; ex-falso)
open import foundation.functions using (id)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We describe conditions under which dependent products are decidable.

```agda
is-decidable-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin {l1} {zero-ℕ} {B} d = inl ind-empty
is-decidable-Π-Fin {l1} {succ-ℕ k} {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin (λ x → d (inl x)))
    ( d (inr star))
```

```agda
is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ m x) → P x) → is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d zero-ℕ (inl H) = inl (λ x → H x (leq-zero-ℕ x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inl H) with d zero-ℕ
... | inr np = inr (λ f → np (f zero-ℕ))
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( inl (λ x → H (succ-ℕ x)))
... | inl g = inl (ind-ℕ p (λ x y → g x))
... | inr ng = inr (λ f → ng (λ x → f (succ-ℕ x)))

{- Corollary 8.2.5 and some variations -}

is-decidable-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-Π-ℕ
    ( λ x → P x → Q x)
    ( λ x → is-decidable-function-type (dP x) (dQ x))
    ( succ-ℕ m)
    ( inl (λ x l p → ex-falso (contradiction-leq-ℕ x m (H x p) l)))

is-decidable-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ x m) → P x)
is-decidable-bounded-Π-ℕ' P d m =
  is-decidable-bounded-Π-ℕ
    ( λ x → leq-ℕ x m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)

is-decidable-strictly-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-strict-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-strictly-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-bounded-Π-ℕ P Q dP dQ m (λ x p → leq-le-ℕ {x} {m} (H x p))

is-decidable-strictly-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → le-ℕ x m → P x)
is-decidable-strictly-bounded-Π-ℕ' P d m =
  is-decidable-strictly-bounded-Π-ℕ
    ( λ x → le-ℕ x m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)
```
