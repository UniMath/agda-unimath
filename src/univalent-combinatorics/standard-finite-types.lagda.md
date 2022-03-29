---
title: The standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.standard-finite-types where

open import elementary-number-theory.equality-natural-numbers using (is-set-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; le-ℕ; transitive-le-ℕ; succ-le-ℕ; preserves-leq-succ-ℕ; refl-leq-ℕ;
    leq-eq-ℕ; concatenate-eq-leq-ℕ; leq-zero-ℕ; neq-le-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-one-ℕ; is-not-one-ℕ)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; eq-is-contr')

open import foundation.booleans using (bool; true; false)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inl-inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.empty-types using (empty; ex-falso)
open import foundation.equality-coproduct-types using (is-emb-inl)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse; map-inv-equiv; map-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap)
open import foundation.injective-maps using (is-injective; is-emb-is-injective)
open import foundation.equivalences-maybe using (equiv-equiv-Maybe)
open import foundation.negation using (¬; map-neg)
open import foundation.non-contractible-types using
  ( is-not-contractible; is-not-contractible-empty)
open import foundation.raising-universe-levels using
  ( raise; equiv-raise; map-raise)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universe-levels using (Level; UU; lzero)
```

## Idea

The standard finite types are defined inductively by `Fin 0 := empty` and `Fin (n+1) := (Fin n) + 1`.

## Definition

### The standard finite types in universe level zero.

```agda
Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

emb-inl-Fin : (k : ℕ) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-inl-Fin k) = inl-Fin k
pr2 (emb-inl-Fin k) = is-emb-inl (Fin k) unit

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

is-neg-one-Fin : {k : ℕ} → Fin k → UU lzero
is-neg-one-Fin {succ-ℕ k} x = Id x neg-one-Fin

neg-two-Fin :
  {k : ℕ} → Fin (succ-ℕ k)
neg-two-Fin {zero-ℕ} = inr star
neg-two-Fin {succ-ℕ k} = inl (inr star)

is-inl-Fin : {k : ℕ} → Fin (succ-ℕ k) → UU lzero
is-inl-Fin {k} x = Σ (Fin k) (λ y → Id (inl y) x)

is-neg-one-is-not-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-inl-Fin x) → is-neg-one-Fin x
is-neg-one-is-not-inl-Fin (inl x) H = ex-falso (H (pair x refl))
is-neg-one-is-not-inl-Fin (inr star) H = refl
```

### The standard finite types in an arbitrary universe

```agda
raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

equiv-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
equiv-raise-Fin l k = equiv-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise
```

## Properties

### Being on the left is decidable

```agda
is-decidable-is-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin x)
is-decidable-is-inl-Fin (inl x) = inl (pair x refl)
is-decidable-is-inl-Fin (inr star) = inr α
  where
  α : is-inl-Fin (inr star) → empty
  α (pair y ())
```

### Fin 1 is contractible

```agda
map-equiv-Fin-one-ℕ : Fin 1 → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin 1
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin 1 ≃ unit
pr1 equiv-Fin-one-ℕ = map-equiv-Fin-one-ℕ
pr2 equiv-Fin-one-ℕ = is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin 1)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  neq-inl-inr (eq-is-contr' C neg-two-Fin neg-one-Fin)
```

### `Fin 2` is equivalent to `bool`

```agda
bool-Fin-two-ℕ : Fin 2 → bool
bool-Fin-two-ℕ (inl (inr star)) = true
bool-Fin-two-ℕ (inr star) = false

Fin-two-ℕ-bool : bool → Fin 2
Fin-two-ℕ-bool true = inl (inr star)
Fin-two-ℕ-bool false = inr star

abstract
  isretr-Fin-two-ℕ-bool : (Fin-two-ℕ-bool ∘ bool-Fin-two-ℕ) ~ id
  isretr-Fin-two-ℕ-bool (inl (inr star)) = refl
  isretr-Fin-two-ℕ-bool (inr star) = refl

abstract
  issec-Fin-two-ℕ-bool : (bool-Fin-two-ℕ ∘ Fin-two-ℕ-bool) ~ id
  issec-Fin-two-ℕ-bool true = refl
  issec-Fin-two-ℕ-bool false = refl

equiv-bool-Fin-two-ℕ : Fin 2 ≃ bool
pr1 equiv-bool-Fin-two-ℕ = bool-Fin-two-ℕ
pr2 equiv-bool-Fin-two-ℕ =
  is-equiv-has-inverse
    ( Fin-two-ℕ-bool)
    ( issec-Fin-two-ℕ-bool)
    ( isretr-Fin-two-ℕ-bool)
```

### The inclusion of Fin k into ℕ

```agda
nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k

upper-bound-nat-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin x) k
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)
upper-bound-nat-Fin {succ-ℕ k} (inr star) = refl-leq-ℕ (succ-ℕ k)

is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl

is-emb-nat-Fin : {k : ℕ} → is-emb (nat-Fin {k})
is-emb-nat-Fin {k} = is-emb-is-injective is-set-ℕ is-injective-nat-Fin

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = nat-Fin
pr2 (emb-nat-Fin k) = is-emb-nat-Fin
```

### The zero elements in the standard finite types

```agda
zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → UU lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

is-zero-Fin' : {k : ℕ} → Fin k → UU lzero
is-zero-Fin' {succ-ℕ k} x = Id zero-Fin x

is-nonzero-Fin : {k : ℕ} → Fin k → UU lzero
is-nonzero-Fin {succ-ℕ k} x = ¬ (is-zero-Fin x)
```

### The successor function on the standard finite types

```agda
skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin
```

```agda
is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (zero-Fin {k}))
is-zero-nat-zero-Fin {zero-ℕ} = refl
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

nat-skip-zero-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (skip-zero-Fin x)) (succ-ℕ (nat-Fin x))
nat-skip-zero-Fin {succ-ℕ k} (inl x) = nat-skip-zero-Fin x
nat-skip-zero-Fin {succ-ℕ k} (inr star) = refl

nat-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (succ-Fin (inl x))) (succ-ℕ (nat-Fin x))
nat-succ-Fin {k} x = nat-skip-zero-Fin x
```

```agda
one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = succ-Fin zero-Fin

is-one-Fin : {k : ℕ} → Fin k → UU lzero
is-one-Fin {succ-ℕ k} x = Id x one-Fin

is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → coprod (is-zero-Fin x) (is-one-Fin x)
is-zero-or-one-Fin-two-ℕ (inl (inr star)) = inl refl
is-zero-or-one-Fin-two-ℕ (inr star) = inr refl

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k
```

```agda
is-injective-inl-Fin : {k : ℕ} → is-injective (inl-Fin k)
is-injective-inl-Fin refl = refl

-- Exercise 7.5 (c)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-Fin (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} ()

-- Exercise 7.5 (d)

is-injective-skip-zero-Fin : {k : ℕ} → is-injective (skip-zero-Fin {k})
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin (is-injective-inl-Fin p))
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inr star} ()
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inl y} ()
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inr star} p = refl

is-injective-succ-Fin : {k : ℕ} → is-injective (succ-Fin {k})
is-injective-succ-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin {k} {x} {y} p)
is-injective-succ-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inr star} p = refl
```

```agda
-- We define a function skip-neg-two-Fin in order to define pred-Fin.

skip-neg-two-Fin :
  {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin {succ-ℕ k} (inl x) = inl (inl x)
skip-neg-two-Fin {succ-ℕ k} (inr x) = neg-one-Fin {succ-ℕ k}

-- We define the predecessor function on Fin k.

pred-Fin : {k : ℕ} → Fin k → Fin k
pred-Fin {succ-ℕ k} (inl x) = skip-neg-two-Fin (pred-Fin x)
pred-Fin {succ-ℕ k} (inr x) = neg-two-Fin

-- We now turn to the exercise.

pred-zero-Fin :
  {k : ℕ} → is-neg-one-Fin (pred-Fin {succ-ℕ k} zero-Fin)
pred-zero-Fin {zero-ℕ} = refl
pred-zero-Fin {succ-ℕ k} = ap skip-neg-two-Fin (pred-zero-Fin {k})

succ-skip-neg-two-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  Id (succ-Fin (skip-neg-two-Fin x)) (inl (succ-Fin x))
succ-skip-neg-two-Fin {zero-ℕ} (inr star) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inl x) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inr star) = refl

issec-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin x)) x
issec-pred-Fin {succ-ℕ zero-ℕ} (inr star) = refl
issec-pred-Fin {succ-ℕ (succ-ℕ k)} (inl x) =
  succ-skip-neg-two-Fin (pred-Fin x) ∙ ap inl (issec-pred-Fin x)
issec-pred-Fin {succ-ℕ (succ-ℕ k)} (inr star) = refl

isretr-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (pred-Fin (succ-Fin x)) x
isretr-pred-Fin {succ-ℕ zero-ℕ} (inr star) = refl
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) =
  ap skip-neg-two-Fin (isretr-pred-Fin (inl x))
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin

is-equiv-succ-Fin : {k : ℕ} → is-equiv (succ-Fin {k})
pr1 (pr1 is-equiv-succ-Fin) = pred-Fin
pr2 (pr1 is-equiv-succ-Fin) = issec-pred-Fin
pr1 (pr2 is-equiv-succ-Fin) = pred-Fin
pr2 (pr2 is-equiv-succ-Fin) = isretr-pred-Fin

equiv-succ-Fin : {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-succ-Fin = succ-Fin
pr2 equiv-succ-Fin = is-equiv-succ-Fin

is-equiv-pred-Fin : {k : ℕ} → is-equiv (pred-Fin {k})
pr1 (pr1 is-equiv-pred-Fin) = succ-Fin
pr2 (pr1 is-equiv-pred-Fin) = isretr-pred-Fin
pr1 (pr2 is-equiv-pred-Fin) = succ-Fin
pr2 (pr2 is-equiv-pred-Fin) = issec-pred-Fin

equiv-pred-Fin : {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-pred-Fin = pred-Fin
pr2 equiv-pred-Fin = is-equiv-pred-Fin
```

```agda
leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (skip-zero-Fin x))
    ( succ-ℕ (nat-Fin (inl x)))
    ( nat-skip-zero-Fin x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (inr star)))
    ( is-zero-nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin {succ-ℕ k} (inr star))))
```

### Fin is injective

```agda
abstract
  is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
  is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
  is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
    ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))
```
