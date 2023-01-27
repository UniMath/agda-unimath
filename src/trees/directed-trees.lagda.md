---
title: Directed trees
---

```agda
module trees.directed-trees where

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.isolated-points
open import foundation.negation
open import foundation.propositions
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

## Idea

A directed tree is a directed graph `G` equipped with a rood `r : G` such that for every vertex `x : G` the type of trails from `x` to `r` is contractible.

## Definition

```agda
is-directed-tree-Graph-Prop :
  {l1 l2 : Level} (G : Graph l1 l2) (r : vertex-Graph G) → Prop (l1 ⊔ l2)
is-directed-tree-Graph-Prop G r =
  Π-Prop
    ( vertex-Graph G)
    ( λ x → is-contr-Prop (walk-Graph G x r))

is-directed-tree-Graph :
  {l1 l2 : Level} (G : Graph l1 l2) (r : vertex-Graph G) → UU (l1 ⊔ l2)
is-directed-tree-Graph G r = type-Prop (is-directed-tree-Graph-Prop G r)

Directed-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Tree l1 l2 =
  Σ ( Graph l1 l2)
    ( λ G →
      Σ ( vertex-Graph G)
        ( λ r → is-directed-tree-Graph G r))

module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  graph-Directed-Tree : Graph l1 l2
  graph-Directed-Tree = pr1 T

  node-Directed-Tree : UU l1
  node-Directed-Tree = vertex-Graph graph-Directed-Tree

  edge-Directed-Tree : (x y : node-Directed-Tree) → UU l2
  edge-Directed-Tree = edge-Graph graph-Directed-Tree

  root-Directed-Tree : node-Directed-Tree
  root-Directed-Tree = pr1 (pr2 T)

  is-directed-tree-Directed-Tree :
    is-directed-tree-Graph graph-Directed-Tree root-Directed-Tree
  is-directed-tree-Directed-Tree = pr2 (pr2 T)
```

## Properties

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2) (r : vertex-Graph G)
  where

  unique-parent-Graph : UU (l1 ⊔ l2)
  unique-parent-Graph =
    (x : vertex-Graph G) →
    is-contr ((r ＝ x) + Σ (vertex-Graph G) (edge-Graph G x))

  no-parent-root-unique-parent-Graph :
    unique-parent-Graph → is-empty (Σ (vertex-Graph G) (edge-Graph G r))
  no-parent-root-unique-parent-Graph H =
    is-empty-right-summand-is-contr-coprod (H r) refl

  is-isolated-root-unique-parent-Graph :
    unique-parent-Graph → is-isolated r
  is-isolated-root-unique-parent-Graph H x =
    map-coprod id (is-empty-left-summand-is-contr-coprod (H x)) (center (H x))

  is-contr-walk-from-root-unique-parent-Graph :
    unique-parent-Graph → is-contr (Σ (vertex-Graph G) (λ y → walk-Graph G r y))
  pr1 (pr1 (is-contr-walk-from-root-unique-parent-Graph H)) = r
  pr2 (pr1 (is-contr-walk-from-root-unique-parent-Graph H)) = refl-walk-Graph
  pr2 (is-contr-walk-from-root-unique-parent-Graph H) (y , refl-walk-Graph) =
    refl
  pr2
    ( is-contr-walk-from-root-unique-parent-Graph H)
    ( y , cons-walk-Graph e w) =
    ex-falso (no-parent-root-unique-parent-Graph H (_ , e))

  is-contr-loop-space-root-unique-parent-Graph :
    unique-parent-Graph → is-contr (r ＝ r)
  is-contr-loop-space-root-unique-parent-Graph H =
    is-contr-loop-space-isolated-point r
      ( is-isolated-root-unique-parent-Graph H)

  is-not-root-has-unique-parent-Graph :
    (x : vertex-Graph G) →
    is-contr ((r ＝ x) + Σ (vertex-Graph G) (edge-Graph G x)) →
    Σ (vertex-Graph G) (edge-Graph G x) → ¬ (r ＝ x)
  is-not-root-has-unique-parent-Graph x H (y , e) =
    is-empty-left-summand-is-contr-coprod H (y , e)

  is-proof-irrelevant-parent-has-unique-parent-Graph :
    (x : vertex-Graph G) →
    is-contr ((r ＝ x) + Σ (vertex-Graph G) (edge-Graph G x)) →
    is-proof-irrelevant (Σ (vertex-Graph G) (edge-Graph G x))
  is-proof-irrelevant-parent-has-unique-parent-Graph x H (y , e) =
    is-contr-right-summand H (y , e)

  is-proof-irrelevant-walk-unique-parent-Graph :
    unique-parent-Graph → (x : vertex-Graph G) →
    is-proof-irrelevant (walk-Graph G x r)
  pr1 (is-proof-irrelevant-walk-unique-parent-Graph H x refl-walk-Graph) =
    refl-walk-Graph
  pr2 (is-proof-irrelevant-walk-unique-parent-Graph H x refl-walk-Graph) w =
    ( inv
      ( ap
        ( λ α → tr (walk-Graph G x) α refl-walk-Graph)
        ( eq-is-contr (is-contr-loop-space-root-unique-parent-Graph H)))) ∙
    ( pr2
      ( pair-eq-Σ
        ( eq-is-contr
          ( is-contr-walk-from-root-unique-parent-Graph H)
          {(r , refl-walk-Graph)}
          {(r , w)})))
  is-proof-irrelevant-walk-unique-parent-Graph H x
    ( cons-walk-Graph {.x} {y} e w) =
    is-contr-equiv
      ( walk-Graph G y r)
      ( equivalence-reasoning
          walk-Graph G x r
          ≃ walk-Graph' G x r
            by compute-walk-Graph G x r
          ≃ Σ (vertex-Graph G) (λ y → edge-Graph G x y × walk-Graph G y r)
            by
            left-unit-law-coprod-is-empty
              ( r ＝ x)
              ( Σ (vertex-Graph G) (λ y → edge-Graph G x y × walk-Graph G y r))
              ( is-not-root-has-unique-parent-Graph x (H x) (y , e))
          ≃ Σ ( Σ (vertex-Graph G) (edge-Graph G x))
              ( λ p → walk-Graph G (pr1 p) r)
            by
            inv-assoc-Σ
              ( vertex-Graph G)
              ( edge-Graph G x)
              ( λ p → walk-Graph G (pr1 p) r)
          ≃ walk-Graph G y r
            by
            left-unit-law-Σ-is-contr
              ( is-proof-irrelevant-parent-has-unique-parent-Graph x
                ( H x)
                ( y , e))
              (y , e))
      ( is-proof-irrelevant-walk-unique-parent-Graph H y w)

  is-directed-tree-unique-parent-Graph :
    unique-parent-Graph → ((x : vertex-Graph G) → walk-Graph G x r) →
    is-directed-tree-Graph G r
  is-directed-tree-unique-parent-Graph H w x =
    is-proof-irrelevant-walk-unique-parent-Graph H x (w x)
```
