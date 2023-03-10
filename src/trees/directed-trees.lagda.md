# Directed trees

```agda
module trees.directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
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
open import foundation.subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

</details>

## Idea

A directed tree is a directed graph `G` equipped with a rood `r : G` such that for every vertex `x : G` the type of trails from `x` to `r` is contractible.

## Definition

```agda
is-tree-Directed-Graph-Prop' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  Prop (l1 ⊔ l2)
is-tree-Directed-Graph-Prop' G r =
  Π-Prop
    ( vertex-Directed-Graph G)
    ( λ x → is-contr-Prop (walk-Directed-Graph G x r))

is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  UU (l1 ⊔ l2)
is-tree-Directed-Graph' G r = type-Prop (is-tree-Directed-Graph-Prop' G r)

is-prop-is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  is-prop (is-tree-Directed-Graph' G r)
is-prop-is-tree-Directed-Graph' G r =
  is-prop-type-Prop (is-tree-Directed-Graph-Prop' G r)

is-tree-Directed-Graph :
  {l1 l2 : Level} → Directed-Graph l1 l2 → UU (l1 ⊔ l2)
is-tree-Directed-Graph G =
  Σ ( vertex-Directed-Graph G)
    ( λ r → is-tree-Directed-Graph' G r)

Directed-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Tree l1 l2 =
  Σ ( Directed-Graph l1 l2) is-tree-Directed-Graph

module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  graph-Directed-Tree : Directed-Graph l1 l2
  graph-Directed-Tree = pr1 T

  node-Directed-Tree : UU l1
  node-Directed-Tree = vertex-Directed-Graph graph-Directed-Tree

  edge-Directed-Tree : (x y : node-Directed-Tree) → UU l2
  edge-Directed-Tree = edge-Directed-Graph graph-Directed-Tree

  walk-Directed-Tree : (x y : node-Directed-Tree) → UU (l1 ⊔ l2)
  walk-Directed-Tree = walk-Directed-Graph graph-Directed-Tree

  is-tree-Directed-Tree : is-tree-Directed-Graph graph-Directed-Tree
  is-tree-Directed-Tree = pr2 T

  root-Directed-Tree : node-Directed-Tree
  root-Directed-Tree = pr1 is-tree-Directed-Tree

  is-tree-Directed-Tree' :
    is-tree-Directed-Graph' graph-Directed-Tree root-Directed-Tree
  is-tree-Directed-Tree' = pr2 is-tree-Directed-Tree

  walk-to-root-Directed-Tree :
    (x : node-Directed-Tree) → walk-Directed-Tree x root-Directed-Tree
  walk-to-root-Directed-Tree x =
    center (is-tree-Directed-Tree' x)
```

## Properties

### Being a tree is a proposition

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  uniqueness-root-is-tree-Directed-Graph :
    (H K : is-tree-Directed-Graph G) → pr1 H ＝ pr1 K
  uniqueness-root-is-tree-Directed-Graph (r , H) (s , K) =
    eq-is-refl-concat-walk-Directed-Graph G
      ( center (K r))
      ( center (H s))
      ( eq-is-contr (H r))

  is-prop-is-tree-Directed-Graph : is-prop (is-tree-Directed-Graph G)
  is-prop-is-tree-Directed-Graph =
    is-prop-all-elements-equal
      ( λ H K →
        eq-type-subtype
          ( is-tree-Directed-Graph-Prop' G)
          ( uniqueness-root-is-tree-Directed-Graph H K))

uniqueness-root-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  (H : is-tree-Directed-Graph (graph-Directed-Tree T)) →
  root-Directed-Tree T ＝ pr1 H
uniqueness-root-Directed-Tree T =
  uniqueness-root-is-tree-Directed-Graph
    ( graph-Directed-Tree T)
    ( is-tree-Directed-Tree T)
```

### Graphs in which vertices have unique parents are trees if for every vertex `x` there is a walk from `x` to the root

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G)
  where

  unique-parent-Directed-Graph : UU (l1 ⊔ l2)
  unique-parent-Directed-Graph =
    (x : vertex-Directed-Graph G) →
    is-contr ((r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))

  no-parent-root-unique-parent-Directed-Graph :
    unique-parent-Directed-Graph →
    is-empty (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G r))
  no-parent-root-unique-parent-Directed-Graph H =
    is-empty-right-summand-is-contr-coprod (H r) refl

  is-isolated-root-unique-parent-Directed-Graph :
    unique-parent-Directed-Graph → is-isolated r
  is-isolated-root-unique-parent-Directed-Graph H x =
    map-coprod id (is-empty-left-summand-is-contr-coprod (H x)) (center (H x))

  is-contr-walk-from-root-unique-parent-Directed-Graph :
    unique-parent-Directed-Graph →
    is-contr (Σ (vertex-Directed-Graph G) (λ y → walk-Directed-Graph G r y))
  pr1 (pr1 (is-contr-walk-from-root-unique-parent-Directed-Graph H)) = r
  pr2 (pr1 (is-contr-walk-from-root-unique-parent-Directed-Graph H)) =
    refl-walk-Directed-Graph
  pr2
    ( is-contr-walk-from-root-unique-parent-Directed-Graph H)
    ( y , refl-walk-Directed-Graph) =
    refl
  pr2
    ( is-contr-walk-from-root-unique-parent-Directed-Graph H)
    ( y , cons-walk-Directed-Graph e w) =
    ex-falso (no-parent-root-unique-parent-Directed-Graph H (_ , e))

  is-contr-loop-space-root-unique-parent-Directed-Graph :
    unique-parent-Directed-Graph → is-contr (r ＝ r)
  is-contr-loop-space-root-unique-parent-Directed-Graph H =
    is-contr-loop-space-isolated-point r
      ( is-isolated-root-unique-parent-Directed-Graph H)

  is-not-root-has-unique-parent-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x) → ¬ (r ＝ x)
  is-not-root-has-unique-parent-Directed-Graph x H (y , e) =
    is-empty-left-summand-is-contr-coprod H (y , e)

  is-proof-irrelevant-parent-has-unique-parent-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    is-proof-irrelevant (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))
  is-proof-irrelevant-parent-has-unique-parent-Directed-Graph x H (y , e) =
    is-contr-right-summand H (y , e)

  is-proof-irrelevant-walk-unique-parent-Directed-Graph :
    unique-parent-Directed-Graph → (x : vertex-Directed-Graph G) →
    is-proof-irrelevant (walk-Directed-Graph G x r)
  pr1
    ( is-proof-irrelevant-walk-unique-parent-Directed-Graph H x
        refl-walk-Directed-Graph) =
    refl-walk-Directed-Graph
  pr2
    ( is-proof-irrelevant-walk-unique-parent-Directed-Graph H x
        refl-walk-Directed-Graph)
    ( w) =
    ( inv
      ( ap
        ( λ α → tr (walk-Directed-Graph G x) α refl-walk-Directed-Graph)
        ( eq-is-contr
          ( is-contr-loop-space-root-unique-parent-Directed-Graph H)))) ∙
    ( pr2
      ( pair-eq-Σ
        ( eq-is-contr
          ( is-contr-walk-from-root-unique-parent-Directed-Graph H)
          {(r , refl-walk-Directed-Graph)}
          {(r , w)})))
  is-proof-irrelevant-walk-unique-parent-Directed-Graph H x
    ( cons-walk-Directed-Graph {.x} {y} e w) =
    is-contr-equiv
      ( walk-Directed-Graph G y r)
      ( equivalence-reasoning
          walk-Directed-Graph G x r
          ≃ walk-Directed-Graph' G x r
            by compute-walk-Directed-Graph G x r
          ≃ Σ ( vertex-Directed-Graph G)
              ( λ y → edge-Directed-Graph G x y × walk-Directed-Graph G y r)
            by
            left-unit-law-coprod-is-empty
              ( r ＝ x)
              ( Σ ( vertex-Directed-Graph G)
                  ( λ y →
                    edge-Directed-Graph G x y × walk-Directed-Graph G y r))
              ( is-not-root-has-unique-parent-Directed-Graph x (H x) (y , e))
          ≃ Σ ( Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))
              ( λ p → walk-Directed-Graph G (pr1 p) r)
            by
            inv-assoc-Σ
              ( vertex-Directed-Graph G)
              ( edge-Directed-Graph G x)
              ( λ p → walk-Directed-Graph G (pr1 p) r)
          ≃ walk-Directed-Graph G y r
            by
            left-unit-law-Σ-is-contr
              ( is-proof-irrelevant-parent-has-unique-parent-Directed-Graph x
                ( H x)
                ( y , e))
              (y , e))
      ( is-proof-irrelevant-walk-unique-parent-Directed-Graph H y w)

  is-tree-unique-parent-Directed-Graph' :
    unique-parent-Directed-Graph →
    ((x : vertex-Directed-Graph G) → walk-Directed-Graph G x r) →
    is-tree-Directed-Graph' G r
  is-tree-unique-parent-Directed-Graph' H w x =
    is-proof-irrelevant-walk-unique-parent-Directed-Graph H x (w x)
```
