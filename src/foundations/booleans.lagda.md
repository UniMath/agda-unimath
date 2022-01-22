---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.booleans where

open import foundations.empty-type using (empty)
open import foundations.identity-types using (Id; refl)
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
