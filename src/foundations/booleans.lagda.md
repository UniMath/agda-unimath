---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.booleans where

open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import foundations.empty-type using (empty)
open import foundations.equivalences using (is-equiv; _≃_)
open import foundations.functions using (id; _∘_; const)
open import foundations.homotopies using (_~_)
open import foundations.identity-types using (Id; refl; inv)
open import foundations.levels using (lzero; UU)
open import foundations.negation using (¬)
open import foundations.unit-type using (unit; star)
```

## The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}
```

### The boolean operators

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

conjunction-bool : bool → (bool → bool)
conjunction-bool true true = true
conjunction-bool true false = false
conjunction-bool false true = false
conjunction-bool false false = false

disjunction-bool : bool → (bool → bool)
disjunction-bool true true = true
disjunction-bool true false = true
disjunction-bool false true = true
disjunction-bool false false = false

-- Exercise 6.2

Eq-bool : bool → bool → UU lzero
Eq-bool true true = unit
Eq-bool true false = empty
Eq-bool false true = empty
Eq-bool false false = unit

refl-Eq-bool : (x : bool) → Eq-bool x x
refl-Eq-bool true = star
refl-Eq-bool false = star

Eq-eq-bool :
  {x y : bool} → Id x y → Eq-bool x y
Eq-eq-bool {x = x} refl = refl-Eq-bool x

eq-Eq-bool :
  {x y : bool} → Eq-bool x y → Id x y
eq-Eq-bool {true} {true} star = refl
eq-Eq-bool {false} {false} star = refl

neq-neg-bool : (b : bool) → ¬ (Id b (neg-bool b))
neq-neg-bool true = Eq-eq-bool
neq-neg-bool false = Eq-eq-bool

neq-false-true-bool :
  ¬ (Id false true)
neq-false-true-bool = Eq-eq-bool
```

```agda
neg-neg-bool : (neg-bool ∘ neg-bool) ~ id
neg-neg-bool true = refl
neg-neg-bool false = refl

abstract
  is-equiv-neg-bool : is-equiv neg-bool
  pr1 (pr1 is-equiv-neg-bool) = neg-bool
  pr2 (pr1 is-equiv-neg-bool) = neg-neg-bool
  pr1 (pr2 is-equiv-neg-bool) = neg-bool
  pr2 (pr2 is-equiv-neg-bool) = neg-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
```

```agda
abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair g G) (pair h H)) =
    neq-false-true-bool (inv (G false))
  not-equiv-const false (pair (pair g G) (pair h H)) =
    neq-false-true-bool (G true)
```
