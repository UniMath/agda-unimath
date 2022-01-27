---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.booleans where

open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.empty-type using (empty; is-prop-empty)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (id; _∘_; const)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; inv)
open import foundation.negation using (¬)
open import foundation.propositions using (is-prop)
open import foundation.sets using (is-set; UU-Set; is-set-prop-in-id)
open import foundation.unit-type using (unit; star; is-prop-unit)
open import foundation.universe-levels using (lzero; UU)
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

## The booleans are a set

```agda
abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = is-prop-unit
  is-prop-Eq-bool true false = is-prop-empty
  is-prop-Eq-bool false true = is-prop-empty
  is-prop-Eq-bool false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool =
    is-set-prop-in-id
      ( Eq-bool)
      ( is-prop-Eq-bool)
      ( refl-Eq-bool)
      ( λ x y → eq-Eq-bool)

bool-Set : UU-Set lzero
pr1 bool-Set = bool
pr2 bool-Set = is-set-bool
```
