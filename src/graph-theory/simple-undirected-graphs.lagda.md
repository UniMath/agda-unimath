# Simple undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.simple-undirected-graphs where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb-Prop)
open import foundation.negation using (¬)
open import foundation.propositions using
  ( UU-Prop; prod-Prop; Π-Prop; function-Prop; is-prop-Prop; type-Prop;
    is-prop-type-Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.unordered-pairs using (unordered-pair)

open import graph-theory.undirected-graphs using
  ( Undirected-Graph; unordered-pair-vertices-Undirected-Graph;
    edge-Undirected-Graph; element-unordered-pair-vertices-Undirected-Graph)

open import univalent-combinatorics.finite-types using (Fin-UU-Fin)
```

## Idea

An undirected graph is said to be simple if it only contains edges between distinct points, and there is at most one edge between any two vertices.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-simple-Undirected-Graph-Prop : UU-Prop (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph-Prop =
    prod-Prop
      ( Π-Prop
        ( unordered-pair-vertices-Undirected-Graph G)
        ( λ p →
          function-Prop
            ( edge-Undirected-Graph G p)
            ( is-emb-Prop
              ( element-unordered-pair-vertices-Undirected-Graph G p))))
      ( Π-Prop
        ( unordered-pair-vertices-Undirected-Graph G)
        ( λ p → is-prop-Prop (edge-Undirected-Graph G p)))

  is-simple-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph = type-Prop is-simple-Undirected-Graph-Prop

  is-prop-is-simple-Undirected-Graph : is-prop is-simple-Undirected-Graph
  is-prop-is-simple-Undirected-Graph =
    is-prop-type-Prop is-simple-Undirected-Graph-Prop

Simple-Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Simple-Undirected-Graph l1 l2 =
  Σ ( UU l1)
    ( λ V →
      Σ ( unordered-pair V → UU-Prop l2)
        ( λ E →
          (x : V) → ¬ (type-Prop (E (pair (Fin-UU-Fin 2) (λ y → x))))))
```
