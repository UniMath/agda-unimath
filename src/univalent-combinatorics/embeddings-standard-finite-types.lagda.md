---
title: Embeddings between standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.embeddings-standard-finite-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import
  elementary-number-theory.repeating-element-standard-finite-type using
  ( repeat-Fin; is-almost-injective-repeat-Fin)

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-injective-inl)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb; is-emb-map-emb; is-emb)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (inv; _∙_; Id; ap)
open import foundation.injective-maps using
  ( is-injective-emb; is-injective-is-emb; is-injective; is-emb-is-injective)
open import foundation.unit-type using (unit; star)

open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin-eq; is-set-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-inl-Fin; is-neg-one-Fin; is-neg-one-is-not-inl-Fin;
    is-decidable-is-inl-Fin)
```

## Idea

Given an embedding `f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)`, we obtain an embedding `Fin k ↪ Fin l`.

## Theorem

```agda
cases-map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
  is-decidable (is-inl-Fin (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin f (inl (pair t p)) x d =
  repeat-Fin t (map-emb f (inl x))
cases-map-reduce-emb-Fin f (inr g) x (inl (pair y p)) = y
cases-map-reduce-emb-Fin f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (is-injective-emb f (p ∙ inv q)))
  where
  p : is-neg-one-Fin (map-emb f (inr star))
  p = is-neg-one-is-not-inl-Fin (map-emb f (inr star)) g
  q : is-neg-one-Fin (map-emb f (inl x))
  q = is-neg-one-is-not-inl-Fin (map-emb f (inl x)) h

map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin f x =
  cases-map-reduce-emb-Fin f
    ( is-decidable-is-inl-Fin (map-emb f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-emb f (inl x)))

abstract
  is-injective-cases-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable  (is-inl-Fin (map-emb f (inl x')))) →
    Id (cases-map-reduce-emb-Fin f d x e) (cases-map-reduce-emb-Fin f d x' e') →
    Id x x'
  is-injective-cases-map-reduce-emb-Fin f (inl (pair t q)) x e x' e' p =
    is-injective-inl
      ( is-injective-is-emb
        ( is-emb-map-emb f)
        ( is-almost-injective-repeat-Fin t
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( p)))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
    is-injective-inl (is-injective-emb f ((inv q) ∙ (ap inl p ∙ q')))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inr h) p =
    ex-falso
    ( Eq-Fin-eq
      ( is-injective-emb f
        ( ( is-neg-one-is-not-inl-Fin (pr1 f (inr star)) g) ∙
          ( inv (is-neg-one-is-not-inl-Fin (pr1 f (inl x')) h)))))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inr h) x' (inl (pair y' q')) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( is-neg-one-is-not-inl-Fin (pr1 f (inr star)) g) ∙
            ( inv (is-neg-one-is-not-inl-Fin (pr1 f (inl x)) h)))))
  is-injective-cases-map-reduce-emb-Fin f (inr g) x (inr h) x' (inr k) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( is-neg-one-is-not-inl-Fin (pr1 f (inr star)) g) ∙
            ( inv (is-neg-one-is-not-inl-Fin (pr1 f (inl x)) h)))))

abstract
  is-injective-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin f)
  is-injective-map-reduce-emb-Fin f {x} {y} =
    is-injective-cases-map-reduce-emb-Fin f
      ( is-decidable-is-inl-Fin (map-emb f (inr star)))
      ( x)
      ( is-decidable-is-inl-Fin (map-emb f (inl x)))
      ( y)
      ( is-decidable-is-inl-Fin (map-emb f (inl y)))

abstract
  is-emb-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin f)
  is-emb-map-reduce-emb-Fin f =
    is-emb-is-injective (is-set-Fin _) (is-injective-map-reduce-emb-Fin f)

reduce-emb-Fin :
  (k l : ℕ) → Fin (succ-ℕ k) ↪ Fin (succ-ℕ l) → Fin k ↪ Fin l
pr1 (reduce-emb-Fin k l f) = map-reduce-emb-Fin f
pr2 (reduce-emb-Fin k l f) = is-emb-map-reduce-emb-Fin f
```
