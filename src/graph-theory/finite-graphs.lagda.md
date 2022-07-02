---
title: Finite graphs
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module graph-theory.finite-graphs where

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.standard-finite-types
```

## Idea

A finite undirected graph consists of a finite set of vertices and a family of finite types of edges indexed by unordered pairs of vertices.

## Definitions

### Finite undirected graphs

```agda
Undirected-Graph-𝔽 : UU (lsuc lzero)
Undirected-Graph-𝔽 = Σ 𝔽 (λ X → unordered-pair (type-𝔽 X) → 𝔽)

module _
  (G : Undirected-Graph-𝔽)
  where

  vertex-Undirected-Graph-𝔽 : UU lzero
  vertex-Undirected-Graph-𝔽 = type-𝔽 (pr1 G)

  unordered-pair-vertices-Undirected-Graph-𝔽 : UU (lsuc lzero)
  unordered-pair-vertices-Undirected-Graph-𝔽 =
    unordered-pair vertex-Undirected-Graph-𝔽

  is-finite-vertex-Undirected-Graph-𝔽 : is-finite vertex-Undirected-Graph-𝔽
  is-finite-vertex-Undirected-Graph-𝔽 = is-finite-type-𝔽 (pr1 G)

  edge-Undirected-Graph-𝔽 :
    (p : unordered-pair-vertices-Undirected-Graph-𝔽) → UU lzero
  edge-Undirected-Graph-𝔽 p = type-𝔽 (pr2 G p)

  is-finite-edge-Undirected-Graph-𝔽 :
    (p : unordered-pair-vertices-Undirected-Graph-𝔽) →
    is-finite (edge-Undirected-Graph-𝔽 p)
  is-finite-edge-Undirected-Graph-𝔽 p = is-finite-type-𝔽 (pr2 G p)

  total-edge-Undirected-Graph-𝔽 : UU (lsuc lzero)
  total-edge-Undirected-Graph-𝔽 =
    Σ unordered-pair-vertices-Undirected-Graph-𝔽 edge-Undirected-Graph-𝔽

  graph-Undirected-Graph-𝔽 : Undirected-Graph lzero lzero
  pr1 graph-Undirected-Graph-𝔽 = vertex-Undirected-Graph-𝔽
  pr2 graph-Undirected-Graph-𝔽 = edge-Undirected-Graph-𝔽
```


### The following type is expected to be equivalent to Undirected-Graph-𝔽

```agda
Undirected-Graph-𝔽' : UU (lsuc lzero)
Undirected-Graph-𝔽' =
  Σ ( 𝔽)
    ( λ V →
      Σ ( type-𝔽 V → type-𝔽 V → 𝔽)
        ( λ E →
          Σ ( (x y : type-𝔽 V) → type-𝔽 (E x y) ≃ type-𝔽 (E y x))
            ( λ σ →
              (x y : type-𝔽 V) → map-equiv ((σ y x) ∘e (σ x y)) ~ id)))
```

The degree of a vertex x of a graph G is the set of occurences of x as an endpoint of x. Note that the unordered pair {x,x} adds two elements to the degree of x.

```agda
incident-edges-vertex-Undirected-Graph-𝔽 :
  (G : Undirected-Graph-𝔽) (x : vertex-Undirected-Graph-𝔽 G) → UU (lsuc lzero)
incident-edges-vertex-Undirected-Graph-𝔽 G x =
  Σ ( unordered-pair (vertex-Undirected-Graph-𝔽 G))
    ( λ p → fib (element-unordered-pair p) x)
```


complete-Undirected-Graph-𝔽 : 𝔽 → Undirected-Graph-𝔽
complete-Undirected-Graph-𝔽 X = complete-multipartite-Undirected-Graph-𝔽 X (λ x → unit-𝔽)

complete-bipartite-Undirected-Graph-𝔽 : 𝔽 → 𝔽 → Undirected-Graph-𝔽
Undirected-Graph-𝔽.vertex (complete-bipartite-Undirected-Graph-𝔽 X Y) = coprod-𝔽 X Y
Undirected-Graph-𝔽.edge (complete-bipartite-Undirected-Graph-𝔽 X Y) p =
  prod-𝔽 ( Σ-𝔽 X
           ( λ x →
             fib-𝔽
               ( two-element-type-𝔽 (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inl x)))
         ( Σ-𝔽 Y
           ( λ y →
             fib-𝔽
               ( two-element-type-𝔽 (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inr y)))
```
