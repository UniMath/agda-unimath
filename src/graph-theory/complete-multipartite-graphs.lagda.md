---
title: Complete multipartite graphs
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.complete-multipartite-graphs where

open import foundation.dependent-pair-types
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

## Idea

A complete multipartite graph consists of a finite list of sets `V1,ā¦,Vn`, and for each unordered pair of distinct elements `i,jā¤n` and each `x : Vi` and `y : Vj` an edge between `x` and `y`.

```agda
complete-multipartite-Undirected-Graph-š½ : (X : š½) (Y : type-š½ X ā š½) ā Undirected-Graph-š½
pr1 (complete-multipartite-Undirected-Graph-š½ X Y) = Ī£-š½ X Y
pr2 (complete-multipartite-Undirected-Graph-š½ X Y) p =
  ( Ī -š½ ( finite-type-2-Element-Type (pr1 p))
        ( Ī» x ā
          Ī -š½ ( finite-type-2-Element-Type (pr1 p))
              ( Ī» y ā
                Id-š½ X
                  ( pr1 (element-unordered-pair p x))
                  ( pr1 (element-unordered-pair p y))))) ā-š½
  empty-š½
```
