# Equivalences between standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equivalences-standard-finite-types where

open import elementary-number-theory.exponentiation-natural-numbers using
  ( exp-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)

open import foundation.contractible-types using (equiv-is-contr)
open import foundation.equivalences using (_≃_; _∘e_; inv-equiv)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.type-arithmetic-empty-type using
  ( inv-left-unit-law-coprod)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universal-property-coproduct-types using
  ( equiv-universal-property-coprod)
open import foundation.universal-property-empty-type using
  ( universal-property-empty')
open import foundation.universal-property-unit-type using
  ( equiv-universal-property-unit)

open import univalent-combinatorics.cartesian-product-types using (prod-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin)
```

## Idea

We construct equivalences between (types built out of) standard finite types.

### The standard finite types are closed under function types

```agda
function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coprod unit) ∘e
  ( equiv-is-contr (universal-property-empty' (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( ( prod-Fin (exp-ℕ l k) l) ∘e
    ( equiv-prod (function-Fin k l) (equiv-universal-property-unit (Fin l)))) ∘e
  ( equiv-universal-property-coprod (Fin l))

Fin-exp-ℕ : (k l : ℕ) → Fin (exp-ℕ l k) ≃ (Fin k → Fin l)
Fin-exp-ℕ k l = inv-equiv (function-Fin k l)
```
