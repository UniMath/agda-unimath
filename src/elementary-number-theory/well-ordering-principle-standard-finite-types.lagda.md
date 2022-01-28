---
title: Univalent Mathematics in Agda
---

# The Well-Ordering Principle of the standard finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module
  elementary-number-theory.well-ordering-principle-standard-finite-types
  where

open import elementary-number-theory.inequality-standard-finite-types using
  ( leq-Fin; leq-neg-one-Fin; refl-leq-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin; inl-Fin; neg-one-Fin)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr; ind-coprod)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-iff)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso; ind-empty)
open import foundation.functions using (_∘_)
open import foundation.negation using (¬)
open import foundation.unit-type using (star; ind-unit)
open import foundation.universe-levels using (Level; UU)
```

# The well-ordering principle on the standard finite types

```agda
exists-not-not-forall-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} → (is-decidable-fam P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-forall-Fin {l} {zero-ℕ} d H = ex-falso (H ind-empty)
exists-not-not-forall-Fin {l} {succ-ℕ k} {P} d H with d (inr star)
... | inl p =
  T ( exists-not-not-forall-Fin
      ( λ x → d (inl x))
      ( λ f → H (ind-coprod P f (ind-unit p))))
  where
  T : Σ (Fin k) (λ x → ¬ (P (inl x))) → Σ (Fin (succ-ℕ k)) (λ x → ¬ (P x))
  T z = pair (inl (pr1 z)) (pr2 z)
... | inr f = pair (inr star) f
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

```agda
is-lower-bound-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → Fin k → UU l
is-lower-bound-Fin {l} {k} P x =
  (y : Fin k) → P y → leq-Fin x y

minimal-element-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → UU l
minimal-element-Fin {l} {k} P =
  Σ (Fin k) (λ x → (P x) × is-lower-bound-Fin P x)

is-lower-bound-inl-Fin :
  {l : Level} {k : ℕ} {P : Fin (succ-ℕ k) → UU l} {x : Fin k} →
  is-lower-bound-Fin (P ∘ inl) x → is-lower-bound-Fin P (inl-Fin k x)
is-lower-bound-inl-Fin H (inl y) p = H y p
is-lower-bound-inl-Fin {l} {k} {P} {x} H (inr star) p =
  ( leq-neg-one-Fin (inl x))

minimal-element-decidable-subtype-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) →
  Σ (Fin k) P → minimal-element-Fin P
pr1 (minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} d (pair (inl x) p)) =
  inl
    ( pr1
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr1
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  pr1
    ( pr2
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr2
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  is-lower-bound-inl-Fin (pr2 (pr2 m))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)
minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} {P} d (pair (inr star) p)
  with
  is-decidable-Σ-Fin (λ t → d (inl t))
... | inl t =
  pair
    ( inl (pr1 m))
    ( pair
      ( pr1 (pr2 m))
      ( is-lower-bound-inl-Fin (pr2 (pr2 m))))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) t
... | inr f =
  pair
    ( inr star)
    ( pair p g)
  where
  g : (y : Fin (succ-ℕ k)) → P y → leq-Fin (neg-one-Fin {k}) y
  g (inl y) q = ex-falso (f (pair y q))
  g (inr star) q = refl-leq-Fin (neg-one-Fin {k})
```
