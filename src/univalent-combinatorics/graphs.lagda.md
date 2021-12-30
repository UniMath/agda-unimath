---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.graphs where

open import univalent-combinatorics.unordered-pairs public

Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph l1 l2 = Σ (UU l1) (λ V → unordered-pair V → UU l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = pr1 G

  edge-Undirected-Graph : unordered-pair vertex-Undirected-Graph → UU l2
  edge-Undirected-Graph = pr2 G

module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  hom-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Undirected-Graph =
    Σ ( vertex-Undirected-Graph G → vertex-Undirected-Graph H)
      ( λ f →
        ( p : unordered-pair (vertex-Undirected-Graph G)) →
        edge-Undirected-Graph G p →
        edge-Undirected-Graph H (map-unordered-pair f p))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (K : Undirected-Graph l5 l6)
  where

  comp-hom-Undirected-Graph :
    hom-Undirected-Graph H K → hom-Undirected-Graph G H →
    hom-Undirected-Graph G K
  pr1 (comp-hom-Undirected-Graph (pair gV gE) (pair fV fE)) = gV ∘ fV
  pr2 (comp-hom-Undirected-Graph (pair gV gE) (pair fV fE)) p e =
    gE (map-unordered-pair fV p) (fE p e)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  id-hom-Undirected-Graph : hom-Undirected-Graph G G
  pr1 id-hom-Undirected-Graph = id
  pr2 id-hom-Undirected-Graph p = id

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  orientation-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  orientation-Undirected-Graph =
    ( p : unordered-pair (vertex-Undirected-Graph G)) →
    edge-Undirected-Graph G p → type-UU-Fin (pr1 p)

  source-edge-orientation-Undirected-Graph :
    orientation-Undirected-Graph →
    (p : unordered-pair (vertex-Undirected-Graph G)) →
    edge-Undirected-Graph G p → vertex-Undirected-Graph G
  source-edge-orientation-Undirected-Graph d (pair X p) e =
    p (d (pair X p) e)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-simple-Undirected-Graph-Prop : UU-Prop (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph-Prop =
    prod-Prop
      ( Π-Prop
        ( unordered-pair (vertex-Undirected-Graph G))
        ( λ p →
          function-Prop (edge-Undirected-Graph G p) (is-emb-Prop (pr2 p))))
      ( Π-Prop
        ( unordered-pair (vertex-Undirected-Graph G))
        ( λ p → is-prop-Prop (edge-Undirected-Graph G p)))

  is-simple-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph = type-Prop is-simple-Undirected-Graph-Prop

  is-prop-is-simple-Undirected-Graph : is-prop is-simple-Undirected-Graph
  is-prop-is-simple-Undirected-Graph =
    is-prop-type-Prop is-simple-Undirected-Graph-Prop
```
