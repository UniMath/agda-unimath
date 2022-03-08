# Standard finite trees

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.standard-finite-trees where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ)

open import foundation.empty-types using (ex-falso)
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
```
