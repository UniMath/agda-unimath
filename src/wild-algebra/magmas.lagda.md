# Magmas

```agda
{-# OPTIONS --without-K --exact-split #-}

module wild-algebra.magmas where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.counting using (count; map-equiv-count)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A magma is a type equipped with a binary operation.

```agda
Magma-UU : (l : Level) → UU (lsuc l)
Magma-UU l = Σ (UU l) (λ A → A → A → A)

type-Magma : {l : Level} → Magma-UU l → UU l
type-Magma M = pr1 M

μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M → type-Magma M → type-Magma M
μ-Magma M = pr2 M

fold-Fin-μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M →
  {k : ℕ} → (Fin k → type-Magma M) → type-Magma M
fold-Fin-μ-Magma M m {zero-ℕ} f = m
fold-Fin-μ-Magma M m {succ-ℕ k} f =
  μ-Magma M (fold-Fin-μ-Magma M m (f ∘ inl)) (f (inr star))

fold-count-μ-Magma' :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} {k : ℕ} → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma' M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv e)

fold-count-μ-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv-count e)

is-unital-Magma : {l : Level} (M : Magma-UU l) → UU l
is-unital-Magma M =
  Σ ( type-Magma M)
    ( λ e →
      ( (x : type-Magma M) → Id (μ-Magma M e x) x) ×
      ( (x : type-Magma M) → Id (μ-Magma M x e) x))

Unital-Magma-UU : (l : Level) → UU (lsuc l)
Unital-Magma-UU l = Σ (Magma-UU l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma-UU l → Magma-UU l
magma-Unital-Magma M = pr1 M
  
is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma-UU l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M

is-semigroup-Magma : {l : Level} → Magma-UU l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (μ-Magma M (μ-Magma M x y) z) (μ-Magma M x (μ-Magma M y z))

is-commutative-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (μ-Magma M x y) (μ-Magma M y x)

is-commutative-monoid-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma-UU l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))
```
