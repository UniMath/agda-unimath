# Embeddings between standard finite types

```agda
module univalent-combinatorics.embeddings-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.repeating-element-standard-finite-type

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An embedding between standard finite types is an embedding `Fin k ↪ Fin l`.

## Definitions

```agda
emb-Fin : (k l : ℕ) → UU lzero
emb-Fin k l = Fin k ↪ Fin l
```

## Properties

### Given an embedding `f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)`, we obtain an embedding `Fin k ↪ Fin l`

```agda
cases-map-reduce-emb-Fin :
  (k l : ℕ) (f : emb-Fin (succ-ℕ k) (succ-ℕ l)) →
  is-decidable (is-inl-Fin l (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin l (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin k l f (inl (pair t p)) x d =
  repeat-Fin l t (map-emb f (inl x))
cases-map-reduce-emb-Fin k l f (inr g) x (inl (pair y p)) = y
cases-map-reduce-emb-Fin k l f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (succ-ℕ k) (is-injective-emb f (p ∙ inv q)))
  where
  p : is-neg-one-Fin (succ-ℕ l) (map-emb f (inr star))
  p = is-neg-one-is-not-inl-Fin l (map-emb f (inr star)) g
  q : is-neg-one-Fin (succ-ℕ l) (map-emb f (inl x))
  q = is-neg-one-is-not-inl-Fin l (map-emb f (inl x)) h

map-reduce-emb-Fin :
  (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin k l f x =
  cases-map-reduce-emb-Fin k l f
    ( is-decidable-is-inl-Fin l (map-emb f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin l (map-emb f (inl x)))

abstract
  is-injective-cases-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin l (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin l (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable (is-inl-Fin l (map-emb f (inl x')))) →
    Id
      ( cases-map-reduce-emb-Fin k l f d x e)
      ( cases-map-reduce-emb-Fin k l f d x' e') →
    x ＝ x'
  is-injective-cases-map-reduce-emb-Fin k l f (inl (pair t q)) x e x' e' p =
    is-injective-inl
      ( is-injective-is-emb
        ( is-emb-map-emb f)
        ( is-almost-injective-repeat-Fin l t
          ( λ α → Eq-Fin-eq (succ-ℕ k) (is-injective-emb f ((inv q) ∙ α)))
          ( λ α → Eq-Fin-eq (succ-ℕ k) (is-injective-emb f ((inv q) ∙ α)))
          ( p)))
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
    is-injective-inl (is-injective-emb f ((inv q) ∙ (ap inl p ∙ q')))
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inl (pair y q)) x' (inr h) p =
    ex-falso
    ( Eq-Fin-eq (succ-ℕ k)
      ( is-injective-emb f
        ( ( is-neg-one-is-not-inl-Fin l (pr1 f (inr star)) g) ∙
          ( inv (is-neg-one-is-not-inl-Fin l (pr1 f (inl x')) h)))))
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inr h) x' (inl (pair y' q')) p =
    ex-falso
      ( Eq-Fin-eq (succ-ℕ k)
        ( is-injective-emb f
          ( ( is-neg-one-is-not-inl-Fin l (pr1 f (inr star)) g) ∙
            ( inv (is-neg-one-is-not-inl-Fin l (pr1 f (inl x)) h)))))
  is-injective-cases-map-reduce-emb-Fin k l f (inr g) x (inr h) x' (inr m) p =
    ex-falso
      ( Eq-Fin-eq (succ-ℕ k)
        ( is-injective-emb f
          ( ( is-neg-one-is-not-inl-Fin l (pr1 f (inr star)) g) ∙
            ( inv (is-neg-one-is-not-inl-Fin l (pr1 f (inl x)) h)))))

abstract
  is-injective-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin k l f)
  is-injective-map-reduce-emb-Fin k l f {x} {y} =
    is-injective-cases-map-reduce-emb-Fin k l f
      ( is-decidable-is-inl-Fin l (map-emb f (inr star)))
      ( x)
      ( is-decidable-is-inl-Fin l (map-emb f (inl x)))
      ( y)
      ( is-decidable-is-inl-Fin l (map-emb f (inl y)))

abstract
  is-emb-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin k l f)
  is-emb-map-reduce-emb-Fin k l f =
    is-emb-is-injective (is-set-Fin l) (is-injective-map-reduce-emb-Fin k l f)

reduce-emb-Fin :
  (k l : ℕ) → emb-Fin (succ-ℕ k) (succ-ℕ l) → emb-Fin k l
pr1 (reduce-emb-Fin k l f) = map-reduce-emb-Fin k l f
pr2 (reduce-emb-Fin k l f) = is-emb-map-reduce-emb-Fin k l f
```

## To do

- Any embedding from `Fin k` into itself is surjective
