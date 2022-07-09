---
title: Generic finite paths
---

```agda
module graph-theory.generic-finite-paths where

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.equality-natural-numbers
  using (is-set-ℕ; has-decidable-equality-ℕ)
open import elementary-number-theory.natural-numbers
  using (ℕ; zero-ℕ; succ-ℕ; has-no-fixed-points-succ-ℕ)

open import foundation.dependent-pair-types using (Σ; _,_; pr1; pr2)
open import foundation.decidable-types using (is-prop-is-decidable)
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

The **generic finite path** on n vertices is an (undirected) graph which represents the generic situation of having n vertices, each connected to the next by a single edge. Pictorially, we may depict this as

~~~
0 → 1 → ... → n
~~~

## Definition

We construct the definition of the generic finite path in stages: The type of vertices is the standard finite type on $n$ elements, but the type of edges needs more care to define.

```agda
module _ (length : ℕ) where
  generic-finite-path-vertex : UU
  generic-finite-path-vertex = Fin length
```

Our encoding of the edges is a bit obfuscated by the use of `fib`, but it boils down to: For an unordered pair of vertices `p`, there is an edge between the two elements of `p` iff there are points `x, y : type-unordered-pair(p)` such that `p(x) = suc(p(y))`.

```agda
  generic-finite-path-edge : unordered-pair generic-finite-path-vertex → UU
  generic-finite-path-edge vertices =
    Σ (type-unordered-pair vertices) λ x →
      fib (nat-Fin ∘ element-unordered-pair vertices)
        (succ-ℕ (nat-Fin (element-unordered-pair vertices x)))

  generic-finite-path-edge-is-finite :
    (vertices : unordered-pair generic-finite-path-vertex) →
    is-finite (generic-finite-path-edge vertices)
  generic-finite-path-edge-is-finite vertices =
    is-finite-Σ (is-finite-mere-equiv (has-two-elements-type-unordered-pair vertices) is-finite-Fin)
      ( λ x → is-finite-Σ (is-finite-mere-equiv (has-two-elements-type-unordered-pair vertices) is-finite-Fin)
        ( λ y → is-finite-is-decidable-Prop (_ , is-set-ℕ _ _) (has-decidable-equality-ℕ _ _)))

  generic-finite-path-Undirected-Graph : Undirected-Graph lzero lzero
  generic-finite-path-Undirected-Graph .pr1 = generic-finite-path-vertex
  generic-finite-path-Undirected-Graph .pr2 = generic-finite-path-edge

  generic-finite-path-Undirected-Graph-𝔽 : Undirected-Graph-𝔽
  generic-finite-path-Undirected-Graph-𝔽 =
    (generic-finite-path-vertex , is-finite-Fin) ,
    (λ vertices → _ , generic-finite-path-edge-is-finite vertices)
```

## Properties

### The generic path has no loops

```agda
  no-loops-generic-finite-path-Undirected-Graph
    : (x : generic-finite-path-vertex)
    → ¬ (generic-finite-path-edge (standard-unordered-pair x x))
  no-loops-generic-finite-path-Undirected-Graph vertex loop with loop
  ... | inl (inr star) , inl (inr star) , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inl (inr star) , inr star       , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inr star       , inl (inr star) , path = has-no-fixed-points-succ-ℕ _ (inv path)
  ... | inr star       , inr star       , path = has-no-fixed-points-succ-ℕ _ (inv path)
```

### Shorter paths are sub-graphs of larger paths

```agda
module _ (len : ℕ) where
  generic-finite-path-initial-segment
    : emb-Undirected-Graph
      (generic-finite-path-Undirected-Graph len)
      (generic-finite-path-Undirected-Graph (succ-ℕ len))
  pr1 generic-finite-path-initial-segment = inl , λ p e → e
  pr2 generic-finite-path-initial-segment = pr2 (emb-inl-Fin _) , λ p → is-emb-id
```

### The generic finite path is connected

```agda
module _ (len : ℕ) where
  generic-finite-path-is-connected-Undirected-Graph
    : is-connected-Undirected-Graph (generic-finite-path-Undirected-Graph len)
  generic-finite-path-is-connected-Undirected-Graph x y = unit-trunc-Prop {!   !}
    where
      patht = path-Undirected-Graph (generic-finite-path-Undirected-Graph len)

      raise-path : ∀ {len} (x y : Fin len) →
        path-Undirected-Graph (generic-finite-path-Undirected-Graph len) x y →
        path-Undirected-Graph (generic-finite-path-Undirected-Graph (succ-ℕ len)) (inl x) (inl y)
      raise-path x .x refl-path-Undirected-Graph = refl-path-Undirected-Graph
      raise-path x _ (cons-path-Undirected-Graph p e prf rest) =
        cons-path-Undirected-Graph (map-unordered-pair inl p) e prf (raise-path _ _ rest)

      find-path-to-top : ∀ {len} (x : Fin (succ-ℕ len)) →
        path-Undirected-Graph (generic-finite-path-Undirected-Graph (succ-ℕ len)) x (inr star)
      find-path-to-top {succ-ℕ len} (inl x) =
        cons-path-Undirected-Graph
          (standard-unordered-pair (inl (inr star)) (inr star))
          (inl (inr star) , (inr star) , refl)
          {y = inl (inr star)} {z = inr star}
          (compute-swap-2-Element-Type _ _ _ λ { () })
          (raise-path _ _ (find-path-to-top x))
      find-path-to-top (inr star) = refl-path-Undirected-Graph

      absurd : ∀ {l} {P : UU l} {k : ℕ} (x : Fin k) → le-ℕ k (nat-Fin x) → P
      absurd {k = zero-ℕ} () p
      absurd {k = succ-ℕ k} (inl x) p = absurd x (le-above-succ-ℕ {k} {nat-Fin x} p)
      absurd {k = succ-ℕ k} (inr x) p = reductio-ad-absurdum (leq-le-ℕ {x = succ-ℕ k} {y = k} p) (neg-succ-leq-ℕ k)

      find-path′
        : ∀ {len} (x y : Fin len) (p : le-ℕ (nat-Fin x) (nat-Fin y))
        → path-Undirected-Graph (generic-finite-path-Undirected-Graph len) x y
      find-path′ {len = succ-ℕ _} (inl x) (inl x₁) p with find-path′ x x₁ p
      ... | path = raise-path _ _ path
      find-path′ {len = succ-ℕ _} (inl x) (inr star) p = find-path-to-top (inl x)
      find-path′ {len = succ-ℕ _} (inr _) (inl f) p = absurd f p
      find-path′ {len = succ-ℕ a} (inr _) (inr _) p = reductio-ad-absurdum p (anti-reflexive-le-ℕ a)

      find-path : (x y : Fin len) → patht x y
      find-path x y with linear-le-ℕ (nat-Fin x) (nat-Fin y)
      ... | inl x<y       = find-path′ x y x<y
      ... | inr (inl x=y) = tr (patht x) (is-injective-nat-Fin x=y) refl-path-Undirected-Graph
      ... | inr (inr y<x) = {! find-path′ y x y<x  !}
```
