---
title: The groupoid of main classes of Latin squares
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.main-classes-of-latin-squares where

open import foundation.universe-levels

open import univalent-combinatorics.main-classes-of-latin-hypercubes
```

## Idea

The groupoid of main classes of latin squares consists of unordered triples of inhabited types equipped with a ternary 1-1 correspondence.

## Definition

```agda
Main-Class-Latin-Squares : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Main-Class-Latin-Squares l1 l2 = Main-Class-Latin-Hypercube l1 l2 2
```
