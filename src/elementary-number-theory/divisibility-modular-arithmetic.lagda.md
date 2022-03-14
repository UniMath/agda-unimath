# Divisibility in modular arithmetic

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.divisibility-modular-arithmetic where

open import elementary-number-theory.divisibility-integers using
  ( refl-div-ℤ; trans-div-ℤ)
open import elementary-number-theory.divisibility-standard-finite-types using
  ( refl-div-Fin; trans-div-Fin)
open import elementary-number-theory.modular-arithmetic using
  ( ℤ-Mod; mul-ℤ-Mod)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

For two numbers `x` and `y` in `ℤ-Mod k`, we say that `x` divides `y` if there is a number `u` in `ℤ-Mod k` such that `mul-ℤ-Mod k u x = y`.

## Definition

```agda
div-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → UU lzero
div-ℤ-Mod k x y = Σ (ℤ-Mod k) (λ u → Id (mul-ℤ-Mod k u x) y)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-ℤ-Mod : {k : ℕ} (x : ℤ-Mod k) → div-ℤ-Mod k x x
refl-div-ℤ-Mod {ℕ.zero-ℕ} = refl-div-ℤ
refl-div-ℤ-Mod {ℕ.succ-ℕ k} = refl-div-Fin
```

### The divisibility relation is transitive

```agda
trans-div-ℤ-Mod :
  {k : ℕ} (x y z : ℤ-Mod k) →
  div-ℤ-Mod k x y → div-ℤ-Mod k y z → div-ℤ-Mod k x z
trans-div-ℤ-Mod {ℕ.zero-ℕ} = trans-div-ℤ
trans-div-ℤ-Mod {ℕ.succ-ℕ k} = trans-div-Fin
```
