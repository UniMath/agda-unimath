---
title: Univalent Mathematics in Agda
---

# The Well-Ordering Principle of the natural numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.well-ordering-principle-natural-numbers where

open import foundation.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-function-type;
    is-decidable-prod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; ex-falso)
open import foundation.functions using (id; _∘_)
open import foundation.identity-types using (Id; refl)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; leq-zero-ℕ; le-ℕ; leq-le-ℕ; contradiction-leq-ℕ; is-decidable-leq-ℕ;
    is-decidable-le-ℕ)
open import foundation.levels using (UU; Level)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; ind-ℕ)
open import foundations.negation using (¬)
open import foundations.unit-type using (star)
```

# Decidable type families on the natural numbers

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

is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-upper-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ m n

is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-strict-upper-bound-ℕ P n =
  (m : ℕ) → P m → le-ℕ m n

is-upper-bound-is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-strict-upper-bound-ℕ P n → is-upper-bound-ℕ P n
is-upper-bound-is-strict-upper-bound-ℕ P n H x p =
  leq-le-ℕ {x} {n} (H x p)

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

## The well-ordering principle of the natural numbers

```agda
{- Definition 8.3.2 -}

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m

{- Theorem 8.3.3 (The well-ordering principle of ℕ) -}

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ex-falso (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-lower-bound-m (succ-ℕ m))
    ( is-lower-bound-m zero-ℕ)
    ( n)
    ( psuccn)

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
pr1 (well-ordering-principle-succ-ℕ P d n p (inl p0) _) = zero-ℕ
pr1 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) = p0
pr2 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) m q = leq-zero-ℕ m
pr1
  ( well-ordering-principle-succ-ℕ P d n p
    (inr neg-p0) (pair m (pair pm is-min-m))) = succ-ℕ m
pr1
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) = pm
pr2
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) =
  is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  Σ ℕ P → minimal-element-ℕ P
pr1 (well-ordering-principle-ℕ P d (pair zero-ℕ p)) = zero-ℕ
pr1 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) = p
pr2 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) m q = leq-zero-ℕ m
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

number-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)

{- Also show that the well-ordering principle returns 0 if P 0 holds,
   independently of the input (pair n p) : Σ ℕ P. -}

is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P zero-ℕ)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P zero-ℕ) →
  Id (pr1 (well-ordering-principle-succ-ℕ P d n p d0 x)) zero-ℕ
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (x : Σ ℕ P) → P zero-ℕ → Id (number-well-ordering-principle-ℕ P d x) zero-ℕ
is-zero-well-ordering-principle-ℕ P d (pair zero-ℕ p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (pair (succ-ℕ m) p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( pair m p))
```

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
