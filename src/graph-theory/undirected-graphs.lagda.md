# Undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.undirected-graphs where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv)
open import foundation.functions using (id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (equiv-tr; ap; refl; tr)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_; lzero)
open import foundation.unordered-pairs using
  ( unordered-pair; map-unordered-pair; type-unordered-pair;
    element-unordered-pair; mere-Eq-unordered-pair; standard-unordered-pair;
    Eq-unordered-pair; eq-Eq-unordered-pair'; refl-Eq-unordered-pair;
    isretr-eq-Eq-unordered-pair)

open import graph-theory.directed-graphs using (Graph; vertex-Graph; edge-Graph)
```

## Idea

An undirected graph consists of a type `V` of vertices and a family `E` of types over the unordered pairs of `V`.

## Definition

```agda
Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph l1 l2 = Σ (UU l1) (λ V → unordered-pair V → UU l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = pr1 G

  unordered-pair-vertices-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph =
    unordered-pair vertex-Undirected-Graph

  type-unordered-pair-vertices-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph → UU lzero
  type-unordered-pair-vertices-Undirected-Graph p = type-unordered-pair p

  element-unordered-pair-vertices-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph) →
    type-unordered-pair-vertices-Undirected-Graph p → vertex-Undirected-Graph
  element-unordered-pair-vertices-Undirected-Graph p = element-unordered-pair p

  edge-Undirected-Graph : unordered-pair-vertices-Undirected-Graph → UU l2
  edge-Undirected-Graph = pr2 G

  total-edge-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Undirected-Graph =
    Σ unordered-pair-vertices-Undirected-Graph edge-Undirected-Graph
```

### The forgetful functor from directed graphs to undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  undirected-graph-Graph : Undirected-Graph l1 l2
  pr1 undirected-graph-Graph = vertex-Graph G
  pr2 undirected-graph-Graph p =
    Σ ( type-unordered-pair p)
      ( λ x →
        Σ ( type-unordered-pair p)
          ( λ y →
            edge-Graph G
              ( element-unordered-pair p x)
              ( element-unordered-pair p y)))

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  graph-Undirected-Graph : Graph l1 (lsuc lzero ⊔ l1 ⊔ l2)
  pr1 graph-Undirected-Graph = vertex-Undirected-Graph G
  pr2 graph-Undirected-Graph x y =
    Σ ( unordered-pair-vertices-Undirected-Graph G)
      ( λ p →
        ( mere-Eq-unordered-pair (standard-unordered-pair x y) p) ×
        ( edge-Undirected-Graph G p))

  graph-Undirected-Graph' : Graph l1 l2
  pr1 graph-Undirected-Graph' = vertex-Undirected-Graph G
  pr2 graph-Undirected-Graph' x y =
    edge-Undirected-Graph G (standard-unordered-pair x y)
```

### Transporting edges along equalities of unordere pairs of vertices

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where
  
  equiv-tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p ≃ edge-Undirected-Graph G q
  equiv-tr-edge-Undirected-Graph p q α =
    equiv-tr (edge-Undirected-Graph G) (eq-Eq-unordered-pair' p q α)

  tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p → edge-Undirected-Graph G q
  tr-edge-Undirected-Graph p q α =
    tr (edge-Undirected-Graph G) (eq-Eq-unordered-pair' p q α)
```
