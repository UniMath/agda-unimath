# Fibers of enriched directed trees

```agda
module trees.fibers-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.enriched-directed-trees
open import trees.fibers-directed-trees
```

</details>

## Idea

The fiber of an enriched directed tree at a node `x` is the fiber of the
underlying directed tree at `x` equipped with the inherited enriched structure.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B) (x : node-Enriched-Directed-Tree A B T)
  where

  directed-tree-fiber-Enriched-Directed-Tree : Directed-Tree (l3 ⊔ l4) (l3 ⊔ l4)
  directed-tree-fiber-Enriched-Directed-Tree =
    fiber-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) x

  node-fiber-Enriched-Directed-Tree : UU (l3 ⊔ l4)
  node-fiber-Enriched-Directed-Tree =
    node-fiber-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) x

  node-inclusion-fiber-Enriched-Directed-Tree :
    node-fiber-Enriched-Directed-Tree → node-Enriched-Directed-Tree A B T
  node-inclusion-fiber-Enriched-Directed-Tree =
    node-inclusion-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  edge-fiber-Enriched-Directed-Tree :
    (y z : node-fiber-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  edge-fiber-Enriched-Directed-Tree =
    edge-fiber-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) x

  shape-fiber-Enriched-Directed-Tree :
    node-fiber-Enriched-Directed-Tree → A
  shape-fiber-Enriched-Directed-Tree y =
    shape-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree y)

  enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree) →
    B (shape-fiber-Enriched-Directed-Tree y) ≃
    Σ ( node-fiber-Enriched-Directed-Tree)
      ( λ z → edge-fiber-Enriched-Directed-Tree z y)
  enrichment-fiber-Enriched-Directed-Tree (y , w) =
    ( interchange-Σ-Σ (λ u e v → v ＝ cons-walk-Directed-Graph e w)) ∘e
    ( ( inv-equiv
        ( right-unit-law-Σ-is-contr
          ( λ i →
            is-contr-total-path' (cons-walk-Directed-Graph (pr2 i) w)))) ∘e
      ( enrichment-Enriched-Directed-Tree A B T y))

  fiber-Enriched-Directed-Tree : Enriched-Directed-Tree (l3 ⊔ l4) (l3 ⊔ l4) A B
  pr1 fiber-Enriched-Directed-Tree = directed-tree-fiber-Enriched-Directed-Tree
  pr1 (pr2 fiber-Enriched-Directed-Tree) = shape-fiber-Enriched-Directed-Tree
  pr2 (pr2 fiber-Enriched-Directed-Tree) =
    enrichment-fiber-Enriched-Directed-Tree
```
