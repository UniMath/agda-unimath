# Sums of natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.sums-of-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; ap-add-ℕ; add-ℕ')
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin)

open import foundation.constant-maps using (const)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (map-equiv)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_; _·r_)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count)
```

## Idea

The values of a map `f : X → ℕ` out of a finite type `X` can be summed up.

## Definition

### Sums of natural numbers indexed by a standard finite type

```agda
sum-Fin-ℕ : {k : ℕ} → (Fin k → ℕ) → ℕ
sum-Fin-ℕ {zero-ℕ} f = zero-ℕ
sum-Fin-ℕ {succ-ℕ k} f = add-ℕ (sum-Fin-ℕ (λ x → f (inl x))) (f (inr star))
```

### Sums of natural numbers indexed by a type equipped with a counting

```agda
sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ (f ∘ (map-equiv e))
```

## Properties

### Sums are invariant under homotopy

```agda
abstract
  htpy-sum-Fin-ℕ :
    {k : ℕ} {f g : Fin k → ℕ} (H : f ~ g) → Id (sum-Fin-ℕ f) (sum-Fin-ℕ g)
  htpy-sum-Fin-ℕ {zero-ℕ} H = refl
  htpy-sum-Fin-ℕ {succ-ℕ k} H =
    ap-add-ℕ
      ( htpy-sum-Fin-ℕ (λ x → H (inl x)))
      ( H (inr star))

abstract
  htpy-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
    Id (sum-count-ℕ e f) (sum-count-ℕ e g)
  htpy-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ (H ·r (map-equiv e))
```

### Summing up the same value `m` times is multiplication by `m`.

```agda
abstract
  constant-sum-Fin-ℕ :
    (m n : ℕ) → Id (sum-Fin-ℕ (const (Fin m) ℕ n)) (mul-ℕ m n)
  constant-sum-Fin-ℕ zero-ℕ n = refl
  constant-sum-Fin-ℕ (succ-ℕ m) n = ap (add-ℕ' n) (constant-sum-Fin-ℕ m n)

abstract
  constant-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) (n : ℕ) →
    Id (sum-count-ℕ e (const A ℕ n)) (mul-ℕ (number-of-elements-count e) n)
  constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n
```

### Finite sums are associative

```agda
abstract
  associative-sum-count-ℕ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
    Id ( sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)))
      ( sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f))
  associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
    ( ( ap-sum-count-ℕ count-A
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
