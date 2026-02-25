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
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.bases-enriched-directed-trees
open import trees.directed-trees
open import trees.enriched-directed-trees
open import trees.fibers-directed-trees
```

</details>

## Idea

The
{{#concept "fiber" Disambiguation="of an enriched directed tree" Agda=fiber-Enriched-Directed-Tree}}
of an [enriched directed tree](trees.enriched-directed-trees.md) at a node `x`
is the [fiber](trees.fibers-directed-trees.md) of the underlying
[directed tree](trees.directed-trees.md) at `x` equipped with the inherited
enriched structure.

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

  walk-node-inclusion-fiber-Enriched-Directed-Tree :
    ( y : node-fiber-Enriched-Directed-Tree) →
    walk-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree y)
      ( x)
  walk-node-inclusion-fiber-Enriched-Directed-Tree =
    walk-node-inclusion-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  edge-fiber-Enriched-Directed-Tree :
    (y z : node-fiber-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  edge-fiber-Enriched-Directed-Tree =
    edge-fiber-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) x

  edge-inclusion-fiber-Enriched-Directed-Tree :
    (y z : node-fiber-Enriched-Directed-Tree) →
    edge-fiber-Enriched-Directed-Tree y z →
    edge-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree y)
      ( node-inclusion-fiber-Enriched-Directed-Tree z)
  edge-inclusion-fiber-Enriched-Directed-Tree =
    edge-inclusion-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  direct-predecessor-fiber-Enriched-Directed-Tree :
    (x : node-fiber-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  direct-predecessor-fiber-Enriched-Directed-Tree =
    direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  shape-fiber-Enriched-Directed-Tree :
    node-fiber-Enriched-Directed-Tree → A
  shape-fiber-Enriched-Directed-Tree y =
    shape-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree y)

  enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree) →
    B (shape-fiber-Enriched-Directed-Tree y) ≃
    direct-predecessor-fiber-Enriched-Directed-Tree y
  enrichment-fiber-Enriched-Directed-Tree (y , w) =
    ( interchange-Σ-Σ (λ u e v → v ＝ cons-walk-Directed-Graph e w)) ∘e
    ( ( inv-right-unit-law-Σ-is-contr
        ( λ i →
          is-torsorial-Id' (cons-walk-Directed-Graph (pr2 i) w))) ∘e
      ( enrichment-Enriched-Directed-Tree A B T y))

  fiber-Enriched-Directed-Tree : Enriched-Directed-Tree (l3 ⊔ l4) (l3 ⊔ l4) A B
  pr1 fiber-Enriched-Directed-Tree = directed-tree-fiber-Enriched-Directed-Tree
  pr1 (pr2 fiber-Enriched-Directed-Tree) = shape-fiber-Enriched-Directed-Tree
  pr2 (pr2 fiber-Enriched-Directed-Tree) =
    enrichment-fiber-Enriched-Directed-Tree

  map-enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree) →
    B ( shape-fiber-Enriched-Directed-Tree y) →
    direct-predecessor-fiber-Enriched-Directed-Tree y
  map-enrichment-fiber-Enriched-Directed-Tree =
    map-enrichment-Enriched-Directed-Tree A B fiber-Enriched-Directed-Tree

  node-enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree)
    (b : B (shape-fiber-Enriched-Directed-Tree y)) →
    node-fiber-Enriched-Directed-Tree
  node-enrichment-fiber-Enriched-Directed-Tree =
    node-enrichment-Enriched-Directed-Tree A B fiber-Enriched-Directed-Tree

  edge-enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree)
    (b : B (shape-fiber-Enriched-Directed-Tree y)) →
    edge-fiber-Enriched-Directed-Tree
      ( node-enrichment-fiber-Enriched-Directed-Tree y b)
      ( y)
  edge-enrichment-fiber-Enriched-Directed-Tree =
    edge-enrichment-Enriched-Directed-Tree A B fiber-Enriched-Directed-Tree

  eq-map-enrichment-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree)
    (b : B (shape-fiber-Enriched-Directed-Tree y)) →
    (w :
      walk-Enriched-Directed-Tree A B T
        ( node-inclusion-fiber-Enriched-Directed-Tree
          ( node-enrichment-fiber-Enriched-Directed-Tree y b))
        ( x)) →
    (p :
      ( w) ＝
      ( cons-walk-Directed-Graph
        ( edge-enrichment-Enriched-Directed-Tree A B T
          ( node-inclusion-fiber-Enriched-Directed-Tree y)
          ( b))
        ( walk-node-inclusion-fiber-Enriched-Directed-Tree y))) →
    ( ( ( node-inclusion-fiber-Enriched-Directed-Tree
          ( node-enrichment-fiber-Enriched-Directed-Tree y b)) ,
        ( w)) ,
      ( edge-inclusion-fiber-Enriched-Directed-Tree
        ( node-enrichment-fiber-Enriched-Directed-Tree y b)
        ( y)
        ( edge-enrichment-fiber-Enriched-Directed-Tree y b)) ,
      ( p)) ＝
    map-enrichment-fiber-Enriched-Directed-Tree y b
  eq-map-enrichment-fiber-Enriched-Directed-Tree y b w p =
    eq-interchange-Σ-Σ-is-contr _
      ( is-torsorial-Id'
        ( cons-walk-Directed-Graph
          ( edge-enrichment-Enriched-Directed-Tree A B T
            ( node-inclusion-fiber-Enriched-Directed-Tree y)
            ( b))
          ( walk-node-inclusion-fiber-Enriched-Directed-Tree y)))
```

### Computing the direct predecessors of a node in a fiber

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  (x : node-Enriched-Directed-Tree A B T)
  where

  compute-direct-predecessor-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree A B T x) →
    direct-predecessor-fiber-Enriched-Directed-Tree A B T x y ≃
    direct-predecessor-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree A B T x y)
  compute-direct-predecessor-fiber-Enriched-Directed-Tree =
    compute-direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  map-compute-direct-predecessor-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree A B T x) →
    direct-predecessor-fiber-Enriched-Directed-Tree A B T x y →
    direct-predecessor-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree A B T x y)
  map-compute-direct-predecessor-fiber-Enriched-Directed-Tree =
    map-compute-direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  inv-compute-direct-predecessor-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree A B T x) →
    direct-predecessor-Enriched-Directed-Tree A B T
      ( node-inclusion-fiber-Enriched-Directed-Tree A B T x y) ≃
    direct-predecessor-fiber-Enriched-Directed-Tree A B T x y
  inv-compute-direct-predecessor-fiber-Enriched-Directed-Tree =
    inv-compute-direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  Eq-direct-predecessor-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree A B T x) →
    (u v : direct-predecessor-fiber-Enriched-Directed-Tree A B T x y) →
    UU (l3 ⊔ l4)
  Eq-direct-predecessor-fiber-Enriched-Directed-Tree =
    Eq-direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)

  eq-Eq-direct-predecessor-fiber-Enriched-Directed-Tree :
    (y : node-fiber-Enriched-Directed-Tree A B T x) →
    ( u v : direct-predecessor-fiber-Enriched-Directed-Tree A B T x y) →
    Eq-direct-predecessor-fiber-Enriched-Directed-Tree y u v → u ＝ v
  eq-Eq-direct-predecessor-fiber-Enriched-Directed-Tree =
    eq-Eq-direct-predecessor-fiber-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( x)
```

### The fiber of a tree at a base node

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  (b : B (shape-root-Enriched-Directed-Tree A B T))
  where

  fiber-base-Enriched-Directed-Tree :
    Enriched-Directed-Tree (l3 ⊔ l4) (l3 ⊔ l4) A B
  fiber-base-Enriched-Directed-Tree =
    fiber-Enriched-Directed-Tree A B T
      ( node-base-Enriched-Directed-Tree A B T b)

  node-fiber-base-Enriched-Directed-Tree : UU (l3 ⊔ l4)
  node-fiber-base-Enriched-Directed-Tree =
    node-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  edge-fiber-base-Enriched-Directed-Tree :
    (x y : node-fiber-base-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  edge-fiber-base-Enriched-Directed-Tree =
    edge-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  root-fiber-base-Enriched-Directed-Tree :
    node-fiber-base-Enriched-Directed-Tree
  root-fiber-base-Enriched-Directed-Tree =
    root-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  walk-fiber-base-Enriched-Directed-Tree :
    (x y : node-fiber-base-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  walk-fiber-base-Enriched-Directed-Tree =
    walk-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  shape-fiber-base-Enriched-Directed-Tree :
    node-fiber-base-Enriched-Directed-Tree → A
  shape-fiber-base-Enriched-Directed-Tree =
    shape-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  enrichment-fiber-base-Enriched-Directed-Tree :
    (y : node-fiber-base-Enriched-Directed-Tree) →
    B (shape-fiber-base-Enriched-Directed-Tree y) ≃
    Σ ( node-fiber-base-Enriched-Directed-Tree)
      ( λ z → edge-fiber-base-Enriched-Directed-Tree z y)
  enrichment-fiber-base-Enriched-Directed-Tree =
    enrichment-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  map-enrichment-fiber-base-Enriched-Directed-Tree :
    (y : node-fiber-base-Enriched-Directed-Tree) →
    B (shape-fiber-base-Enriched-Directed-Tree y) →
    Σ ( node-fiber-base-Enriched-Directed-Tree)
      ( λ z → edge-fiber-base-Enriched-Directed-Tree z y)
  map-enrichment-fiber-base-Enriched-Directed-Tree =
    map-enrichment-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree

  directed-tree-fiber-base-Enriched-Directed-Tree :
    Directed-Tree (l3 ⊔ l4) (l3 ⊔ l4)
  directed-tree-fiber-base-Enriched-Directed-Tree =
    directed-tree-Enriched-Directed-Tree A B fiber-base-Enriched-Directed-Tree
```
