---
title: Generic finite paths
---

```agda
{-# OPTIONS --without-K --exact-split #-}
module graph-theory.standard-finite-paths where

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.equality-natural-numbers
  using (has-decidable-equality-ℕ)
open import elementary-number-theory.natural-numbers
  using (ℕ; is-set-ℕ; zero-ℕ; succ-ℕ; has-no-fixed-points-succ-ℕ)

open import foundation.dependent-pair-types using (Σ; _,_; pr1; pr2)
open import foundation.decidable-propositions using (is-finite-is-decidable-Prop)
open import foundation.universe-levels using (UU ; lzero)
open import foundation.fibers-of-maps using (fib)
open import foundation.unordered-pairs
  using ( unordered-pair; standard-unordered-pair; element-unordered-pair;
          type-unordered-pair; eq-Eq-unordered-pair;
          has-two-elements-type-unordered-pair;
          map-unordered-pair)
open import foundation.identity-types using (_＝_; refl; ap; inv; _∙_; tr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.unit-type using (star)
open import foundation.embeddings using (is-emb-id)
open import foundation.propositional-truncations using (unit-trunc-Prop)
open import foundation.functions using (_∘_)
open import foundation.equivalences using (id-equiv)
open import foundation.negation using (¬; reductio-ad-absurdum)

open import graph-theory.embeddings-undirected-graphs
open import graph-theory.connected-undirected-graphs
open import graph-theory.morphisms-undirected-graphs
open import graph-theory.paths-undirected-graphs
open import graph-theory.undirected-graphs
open import graph-theory.finite-graphs

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
```

## Idea

The **standard finite path** on n vertices is an (undirected) graph which represents the generic situation of having n vertices, each connected to the next by a single edge. Pictorially, we may depict this as

~~~
0 → 1 → ... → n
~~~

## Definition

We construct the standard finite path in stages: The type of vertices is the standard finite type on $n$ elements, but the type of edges needs more care to define.

```agda
module _ (length : ℕ) where
  vertex-standard-finite-path : UU
  vertex-standard-finite-path = Fin length
```

Our encoding of the edges is a bit obfuscated by the use of `fib`, but it boils down to: For an unordered pair of vertices `p`, there is an edge between the two elements of `p` iff there are points `x, y : type-unordered-pair(p)` such that `p(x) = suc(p(y))`.

```agda
  edge-standard-finite-path : unordered-pair vertex-standard-finite-path → UU
  edge-standard-finite-path vertices =
    Σ (type-unordered-pair vertices) λ x →
      fib (nat-Fin length ∘ element-unordered-pair vertices)
        (succ-ℕ (nat-Fin length (element-unordered-pair vertices x)))

  is-finite-edge-standard-finite-path :
    (vertices : unordered-pair vertex-standard-finite-path) →
    is-finite (edge-standard-finite-path vertices)
  is-finite-edge-standard-finite-path vertices =
    is-finite-Σ (is-finite-mere-equiv (has-two-elements-type-unordered-pair vertices) (is-finite-Fin 2))
      ( λ x → is-finite-Σ (is-finite-mere-equiv (has-two-elements-type-unordered-pair vertices) (is-finite-Fin 2))
        ( λ y → is-finite-is-decidable-Prop (_ , is-set-ℕ _ _) (has-decidable-equality-ℕ _ _)))

  standard-finite-path-Undirected-Graph : Undirected-Graph lzero lzero
  standard-finite-path-Undirected-Graph .pr1 = vertex-standard-finite-path
  standard-finite-path-Undirected-Graph .pr2 = edge-standard-finite-path

  standard-finite-path-Undirected-Graph-𝔽 : Undirected-Graph-𝔽
  standard-finite-path-Undirected-Graph-𝔽 =
    (vertex-standard-finite-path , is-finite-Fin length) ,
    (λ vertices → _ , is-finite-edge-standard-finite-path vertices)
```

## Properties

### The generic path has no loops

```agda
  no-loops-standard-finite-path-Undirected-Graph
    : (x : vertex-standard-finite-path)
    → ¬ (edge-standard-finite-path (standard-unordered-pair x x))
  no-loops-standard-finite-path-Undirected-Graph vertex loop with loop
  ... | inl (inr star) , inl (inr star) , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inl (inr star) , inr star       , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inr star       , inl (inr star) , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inr star       , inr star       , path = has-no-fixed-points-succ-ℕ _ (inv path)
```

### Shorter paths are sub-graphs of larger paths

```agda
module _ (len : ℕ) where
  standard-finite-path-initial-segment
    : emb-Undirected-Graph
      (standard-finite-path-Undirected-Graph len)
      (standard-finite-path-Undirected-Graph (succ-ℕ len))
  pr1 standard-finite-path-initial-segment = inl , λ p e → e
  pr2 standard-finite-path-initial-segment = pr2 (emb-inl-Fin len) , λ p → is-emb-id
```

### The generic finite path is connected

```agda
module _ (len : ℕ) where
  is-connected-standard-finite-path
    : is-connected-Undirected-Graph (standard-finite-path-Undirected-Graph len)
  is-connected-standard-finite-path x y = unit-trunc-Prop (find-path x y)
    where
      patht = path-Undirected-Graph (standard-finite-path-Undirected-Graph len)

      raise-path : ∀ {len} (x y : Fin len) →
        path-Undirected-Graph (standard-finite-path-Undirected-Graph len) x y →
        path-Undirected-Graph (standard-finite-path-Undirected-Graph (succ-ℕ len)) (inl x) (inl y)
      raise-path x .x refl-path-Undirected-Graph = refl-path-Undirected-Graph
      raise-path x _ (cons-path-Undirected-Graph p e prf rest) =
        cons-path-Undirected-Graph (map-unordered-pair inl p) e prf (raise-path _ _ rest)

      find-path-to-top : ∀ {len} (x : Fin (succ-ℕ len)) →
        path-Undirected-Graph (standard-finite-path-Undirected-Graph (succ-ℕ len)) x (inr star)
      find-path-to-top {succ-ℕ len} (inl x) =
        cons-path-Undirected-Graph
          (standard-unordered-pair (inl (inr star)) (inr star))
          (inl (inr star) , (inr star) , refl)
          {y = inl (inr star)} {z = inr star}
          (compute-swap-2-Element-Type _ _ _ λ { () })
          (raise-path _ _ (find-path-to-top x))
      find-path-to-top {succ-ℕ _} (inr star) = refl-path-Undirected-Graph
      find-path-to-top {zero-ℕ} (inr star) = refl-path-Undirected-Graph

      absurd : ∀ {l} {P : UU l} {k : ℕ} (x : Fin k) → le-ℕ k (nat-Fin k x) → P
      absurd {k = zero-ℕ} () p
      absurd {k = succ-ℕ k} (inl x) p = absurd {k = k} x (le-above-succ-ℕ {k} {nat-Fin k x} p)
      absurd {k = succ-ℕ k} (inr x) p = reductio-ad-absurdum (leq-le-ℕ {x = succ-ℕ k} {y = k} p) (neg-succ-leq-ℕ k)

      find-path′
        : ∀ {len} (x y : Fin len) (p : le-ℕ (nat-Fin len x) (nat-Fin len y))
        → path-Undirected-Graph (standard-finite-path-Undirected-Graph len) x y
      find-path′ {len = succ-ℕ len} (inl x) (inl x₁) p with find-path′ {len = len} x x₁ p
      ... | path = raise-path _ _ path
      find-path′ {len = succ-ℕ _} (inl x) (inr star) p = find-path-to-top (inl x)
      find-path′ {len = succ-ℕ len} (inr _) (inl f) p = absurd {k = len} f p
      find-path′ {len = succ-ℕ a} (inr _) (inr _) p = reductio-ad-absurdum p (anti-reflexive-le-ℕ a)

      find-path : (x y : Fin len) → patht x y
      find-path x y with linear-le-ℕ (nat-Fin len x) (nat-Fin len y)
      ... | inl x<y       = find-path′ {len = len} x y x<y
      ... | inr (inl x=y) = tr (patht x) (is-injective-nat-Fin len x=y) refl-path-Undirected-Graph
      ... | inr (inr y<x) = {! find-path′ y x y<x  !}
```
