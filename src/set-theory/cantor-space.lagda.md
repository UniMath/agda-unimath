---
title: Cantor space
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module set-theory.cantor-space where

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

## Idea

The Cantor space is the type of functions `ℕ → Fin 2`.

## Definition

```agda
cantor-space : UU lzero
cantor-space = ℕ → Fin 2
```
