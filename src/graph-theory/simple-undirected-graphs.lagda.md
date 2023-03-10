# Simple undirected graphs

```agda
module graph-theory.simple-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An undirected graph is said to be simple if it only contains edges between distinct points, and there is at most one edge between any two vertices.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-simple-Undirected-Graph-Prop : Prop (lsuc lzero ⊔ l1 ⊔ l2)
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
      Σ ( unordered-pair V → Prop l2)
        ( λ E →
          (x : V) → ¬ (type-Prop (E (pair (Fin-UU-Fin' 2) (λ y → x))))))
```
