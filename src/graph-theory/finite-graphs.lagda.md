---
title: Formalisation of the Symmetry Book
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

## Definitions

### Undirected graph structures on `Fin n`

```agda
record Graph-Fin : UU (lsuc lzero)
  where
  field
    V : ℕ
    E : (unordered-pair (Fin V)) → ℕ
```

### Directed graph structures on `Fin n`

```agda
record Graph-Fin' : UU (lsuc lzero)
  where
  field
    V : ℕ
    E : Fin V → Fin V → ℕ
    σ : (x y : Fin V) → Id (E x y) (E y x)
```

### Finite undirected graphs

```agda
Graph-𝔽 : UU (lsuc lzero)
Graph-𝔽 = Σ 𝔽 (λ X → unordered-pair (type-𝔽 X) → 𝔽)

module _
  (G : Graph-𝔽)
  where

  vertex-Graph-𝔽 : UU lzero
  vertex-Graph-𝔽 = type-𝔽 (pr1 G)

  unordered-pair-vertices-Graph-𝔽 : UU (lsuc lzero)
  unordered-pair-vertices-Graph-𝔽 = unordered-pair vertex-Graph-𝔽

  is-finite-vertex-Graph-𝔽 : is-finite vertex-Graph-𝔽
  is-finite-vertex-Graph-𝔽 = is-finite-type-𝔽 (pr1 G)

  edge-Graph-𝔽 : (p : unordered-pair-vertices-Graph-𝔽) → UU lzero
  edge-Graph-𝔽 p = type-𝔽 (pr2 G p)

  is-finite-edge-Graph-𝔽 :
    (p : unordered-pair-vertices-Graph-𝔽) → is-finite (edge-Graph-𝔽 p)
  is-finite-edge-Graph-𝔽 p = is-finite-type-𝔽 (pr2 G p)

  total-edge-Graph-𝔽 : UU (lsuc lzero)
  total-edge-Graph-𝔽 = Σ unordered-pair-vertices-Graph-𝔽 edge-Graph-𝔽

  graph-Graph-𝔽 : Undirected-Graph lzero lzero
  pr1 graph-Graph-𝔽 = vertex-Graph-𝔽
  pr2 graph-Graph-𝔽 = edge-Graph-𝔽
```


### The following type is expected to be equivalent to Graph-𝔽

```agda
record Graph-𝔽' : UU (lsuc lzero)
  where
  field
    vertex : 𝔽
    edge : type-𝔽 vertex → type-𝔽 vertex → 𝔽
    σ : (x y : type-𝔽 vertex) → type-𝔽 (edge x y) ≃ type-𝔽 (edge y x)
    σ² : (x y : type-𝔽 vertex) → map-equiv ((σ y x) ∘e (σ x y)) ~ id
```

The degree of a vertex x of a graph G is the set of occurences of x as an endpoint of x. Note that the unordered pair {x,x} adds two elements to the degree of x.

```agda
incident-edges-vertex-Graph-𝔽 :
  (G : Graph-𝔽) (x : vertex-Graph-𝔽 G) → UU (lsuc lzero)
incident-edges-vertex-Graph-𝔽 G x =
  Σ ( unordered-pair (vertex-Graph-𝔽 G))
    ( λ p → fib (element-unordered-pair p) x)
```


{- We formalize the definitions of complete multipartite graphs, complete
   graphs, and complete bipartite graphs. -}

two-element-type-𝔽 : UU-Fin 2 → 𝔽
two-element-type-𝔽 X =
  pair (pr1 X) (is-finite-has-finite-cardinality (pair 2 (pr2 X)))

complete-multipartite-Graph-𝔽 : (X : 𝔽) (Y : type-𝔽 X → 𝔽) → Graph-𝔽
Graph-𝔽.vertex (complete-multipartite-Graph-𝔽 X Y) = Σ-𝔽 X Y
Graph-𝔽.edge (complete-multipartite-Graph-𝔽 X Y) p =
  ( Π-𝔽 ( two-element-type-𝔽 (pr1 p))
        ( λ x →
          Π-𝔽 ( two-element-type-𝔽 (pr1 p))
              ( λ y →
                Id-𝔽 X
                  ( pr1 (element-unordered-pair p x))
                  ( pr1 (element-unordered-pair p y))))) →-𝔽
  empty-𝔽

complete-Graph-𝔽 : 𝔽 → Graph-𝔽
complete-Graph-𝔽 X = complete-multipartite-Graph-𝔽 X (λ x → unit-𝔽)

complete-bipartite-Graph-𝔽 : 𝔽 → 𝔽 → Graph-𝔽
Graph-𝔽.vertex (complete-bipartite-Graph-𝔽 X Y) = coprod-𝔽 X Y
Graph-𝔽.edge (complete-bipartite-Graph-𝔽 X Y) p =
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
