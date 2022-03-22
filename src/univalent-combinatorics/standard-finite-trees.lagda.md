# Standard finite trees

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.standard-finite-trees where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ; is-zero-ℕ)
open import elementary-number-theory.sums-of-natural-numbers using (sum-Fin-ℕ)
open import elementary-number-theory.maximum-natural-numbers using (max-Fin-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod)
open import foundation.empty-types using (ex-falso; empty)
open import foundation.identity-types using (Id)
open import foundation.unit-type using (unit)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A standard finite tree is a finite tree that branches by standard finite sets. In contexts where one wouldn't be interested in considering finite trees to be the same if they differ up to a permutation of trees, people simply call our standard finite trees finite trees. From a univalent perspective, however, a finite tree is a tree built out of finite types, not just the standard finite types. Sometimes, standard finite trees are called planar finite trees, to emphasize that the branching types `Fin n` record the order in which the branches occur.

## Definition

```agda
data Tree-Fin : UU lzero where
  tree-Fin : (n : ℕ) → (Fin n → Tree-Fin) → Tree-Fin

root-Tree-Fin : Tree-Fin
root-Tree-Fin = tree-Fin zero-ℕ ex-falso

number-nodes-Tree-Fin : Tree-Fin → ℕ
number-nodes-Tree-Fin (tree-Fin zero-ℕ _) = zero-ℕ
number-nodes-Tree-Fin (tree-Fin (succ-ℕ n) f) = succ-ℕ (sum-Fin-ℕ (λ k → number-nodes-Tree-Fin (f k)))

height-Tree-Fin : Tree-Fin → ℕ
height-Tree-Fin (tree-Fin zero-ℕ f) = zero-ℕ
height-Tree-Fin (tree-Fin (succ-ℕ n) f) = succ-ℕ (max-Fin-ℕ (succ-ℕ n) (λ k → height-Tree-Fin (f k)))

is-leaf-Tree-Fin : Tree-Fin → UU lzero
is-leaf-Tree-Fin (tree-Fin zero-ℕ _) = unit
is-leaf-Tree-Fin (tree-Fin (succ-ℕ n) _) = empty

is-full-binary-Tree-Fin : Tree-Fin → UU lzero
is-full-binary-Tree-Fin (tree-Fin zero-ℕ f) = unit
is-full-binary-Tree-Fin (tree-Fin (succ-ℕ n) f) = (Id 2 n) × ((k : Fin (succ-ℕ n)) → is-full-binary-Tree-Fin (f k))
```
