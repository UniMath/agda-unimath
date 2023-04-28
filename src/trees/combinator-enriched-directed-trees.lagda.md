# Combinators of enriched directed trees

```agda
module trees.combinator-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import trees.bases-enriched-directed-trees
open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.fibers-enriched-directed-trees
open import trees.morphisms-directed-trees
open import trees.morphisms-enriched-directed-trees
```

</details>

## Idea

The **combinator operation** on enriched directed trees combines, for any
element `a : A`, a family of enriched directed trees
`T : B(a) → Enriched-Directed-Tree A B` indexed by `B a` into a single tree
enriched directed tree with a new root.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A}
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  directed-tree-combinator-Enriched-Directed-Tree :
    Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3 ⊔ l4)
  directed-tree-combinator-Enriched-Directed-Tree =
    combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

  node-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3)
  node-combinator-Enriched-Directed-Tree =
    node-combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

  node-inclusion-combinator-Enriched-Directed-Tree :
    (b : B a) → node-Enriched-Directed-Tree A B (T b) →
    node-combinator-Enriched-Directed-Tree
  node-inclusion-combinator-Enriched-Directed-Tree =
    node-inclusion-combinator-Directed-Tree

  root-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree
  root-combinator-Enriched-Directed-Tree = root-combinator-Directed-Tree

  edge-combinator-Enriched-Directed-Tree :
    (x y : node-combinator-Enriched-Directed-Tree) → UU (l2 ⊔ l3 ⊔ l4)
  edge-combinator-Enriched-Directed-Tree =
    edge-combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

  graph-combinator-Enriched-Directed-Tree :
    Directed-Graph (l2 ⊔ l3) (l2 ⊔ l3 ⊔ l4)
  graph-combinator-Enriched-Directed-Tree =
    graph-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  directed-tree-inclusion-combinator-Enriched-Directed-Tree :
    (b : B a) →
    hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B (T b))
      ( directed-tree-combinator-Enriched-Directed-Tree)
  directed-tree-inclusion-combinator-Enriched-Directed-Tree =
    inclusion-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  walk-combinator-Enriched-Directed-Tree :
    (x y : node-combinator-Enriched-Directed-Tree) → UU (l2 ⊔ l3 ⊔ l4)
  walk-combinator-Enriched-Directed-Tree =
    walk-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  walk-inclusion-combinator-Enriched-Directed-Tree :
    (b : B a) (x y : node-Enriched-Directed-Tree A B (T b)) →
    walk-Enriched-Directed-Tree A B (T b) x y →
    walk-combinator-Enriched-Directed-Tree
      ( node-inclusion-combinator-Enriched-Directed-Tree b x)
      ( node-inclusion-combinator-Enriched-Directed-Tree b y)
  walk-inclusion-combinator-Enriched-Directed-Tree =
    walk-inclusion-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  walk-to-root-combinator-Enriched-Directed-Tree :
    (x : node-combinator-Enriched-Directed-Tree) →
    walk-combinator-Enriched-Directed-Tree x
      root-combinator-Enriched-Directed-Tree
  walk-to-root-combinator-Enriched-Directed-Tree =
    walk-to-root-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-root-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree → UU (l2 ⊔ l3)
  is-root-combinator-Enriched-Directed-Tree =
    is-root-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  unique-parent-combinator-Enriched-Directed-Tree :
    unique-parent-Directed-Graph
      ( graph-combinator-Enriched-Directed-Tree)
      ( root-combinator-Enriched-Directed-Tree)
  unique-parent-combinator-Enriched-Directed-Tree =
    unique-parent-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-tree-combinator-Enriched-Directed-Tree :
    is-tree-Directed-Graph graph-combinator-Enriched-Directed-Tree
  is-tree-combinator-Enriched-Directed-Tree =
    is-tree-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  base-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3 ⊔ l4)
  base-combinator-Enriched-Directed-Tree =
    base-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-proper-node-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree → UU (l2 ⊔ l3)
  is-proper-node-combinator-Enriched-Directed-Tree =
    is-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  proper-node-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3)
  proper-node-combinator-Enriched-Directed-Tree =
    proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-proper-node-inclusion-combinator-Enriched-Directed-Tree :
    {b : B a} {x : node-Enriched-Directed-Tree A B (T b)} →
    is-proper-node-combinator-Enriched-Directed-Tree
      ( node-inclusion-combinator-Enriched-Directed-Tree b x)
  is-proper-node-inclusion-combinator-Enriched-Directed-Tree =
    is-proper-node-inclusion-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  shape-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree → A
  shape-combinator-Enriched-Directed-Tree root-combinator-Directed-Tree = a
  shape-combinator-Enriched-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b x) =
    shape-Enriched-Directed-Tree A B (T b) x

  map-root-enrichment-combinator-Enriched-Directed-Tree :
    B a →
    Σ ( node-combinator-Enriched-Directed-Tree)
      ( λ y →
        edge-combinator-Enriched-Directed-Tree y root-combinator-Directed-Tree)
  pr1 (map-root-enrichment-combinator-Enriched-Directed-Tree b) =
    node-inclusion-combinator-Directed-Tree b
      ( root-Enriched-Directed-Tree A B (T b))
  pr2 (map-root-enrichment-combinator-Enriched-Directed-Tree b) =
    edge-to-root-combinator-Directed-Tree b

  map-inv-root-enrichment-combinator-Enriched-Directed-Tree :
    Σ ( node-combinator-Enriched-Directed-Tree)
      ( λ y →
        edge-combinator-Enriched-Directed-Tree y
          root-combinator-Directed-Tree) →
    B a
  map-inv-root-enrichment-combinator-Enriched-Directed-Tree
    (._ , edge-to-root-combinator-Directed-Tree b) = b

  issec-map-inv-root-enrichment-combinator-Enriched-Directed-Tree :
    ( map-root-enrichment-combinator-Enriched-Directed-Tree ∘
      map-inv-root-enrichment-combinator-Enriched-Directed-Tree) ~ id
  issec-map-inv-root-enrichment-combinator-Enriched-Directed-Tree
    ( ._ , edge-to-root-combinator-Directed-Tree b) = refl

  isretr-map-inv-root-enrichment-combinator-Enriched-Directed-Tree :
    ( map-inv-root-enrichment-combinator-Enriched-Directed-Tree ∘
      map-root-enrichment-combinator-Enriched-Directed-Tree) ~ id
  isretr-map-inv-root-enrichment-combinator-Enriched-Directed-Tree b = refl

  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Tree :
    is-equiv map-root-enrichment-combinator-Enriched-Directed-Tree
  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Tree =
    is-equiv-has-inverse
      map-inv-root-enrichment-combinator-Enriched-Directed-Tree
      issec-map-inv-root-enrichment-combinator-Enriched-Directed-Tree
      isretr-map-inv-root-enrichment-combinator-Enriched-Directed-Tree

  root-enrichment-combinator-Enriched-Directed-Tree :
    B a ≃
    Σ ( node-combinator-Enriched-Directed-Tree)
      ( λ y →
        edge-combinator-Enriched-Directed-Tree y root-combinator-Directed-Tree)
  pr1 root-enrichment-combinator-Enriched-Directed-Tree =
    map-root-enrichment-combinator-Enriched-Directed-Tree
  pr2 root-enrichment-combinator-Enriched-Directed-Tree =
    is-equiv-map-root-enrichment-combinator-Enriched-Directed-Tree

  enrichment-combinator-Enriched-Directed-Tree :
    (x : node-combinator-Enriched-Directed-Tree) →
    B (shape-combinator-Enriched-Directed-Tree x) ≃
    Σ ( node-combinator-Enriched-Directed-Tree)
      ( λ y → edge-combinator-Enriched-Directed-Tree y x)
  enrichment-combinator-Enriched-Directed-Tree root-combinator-Directed-Tree =
    root-enrichment-combinator-Enriched-Directed-Tree
  enrichment-combinator-Enriched-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b x) =
    ( compute-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T) b x) ∘e
    ( enrichment-Enriched-Directed-Tree A B (T b) x)

  combinator-Enriched-Directed-Tree :
    Enriched-Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3 ⊔ l4) A B
  pr1 combinator-Enriched-Directed-Tree =
    directed-tree-combinator-Enriched-Directed-Tree
  pr1 (pr2 combinator-Enriched-Directed-Tree) =
    shape-combinator-Enriched-Directed-Tree
  pr2 (pr2 combinator-Enriched-Directed-Tree) =
    enrichment-combinator-Enriched-Directed-Tree
```

## Properties

### The type of children of `x : T b` is equivalent to the type of children of the inclusion of `x` in `combinator T`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A} (b : B a)
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  (x : node-Enriched-Directed-Tree A B (T b))
  where

  children-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3 ⊔ l4)
  children-combinator-Enriched-Directed-Tree =
    children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  map-children-combinator-Enriched-Directed-Tree :
    children-Enriched-Directed-Tree A B (T b) x →
    children-combinator-Enriched-Directed-Tree
  map-children-combinator-Enriched-Directed-Tree =
    map-compute-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  is-equiv-map-children-combinator-Enriched-Directed-Tree :
    is-equiv map-children-combinator-Enriched-Directed-Tree
  is-equiv-map-children-combinator-Enriched-Directed-Tree =
    is-equiv-map-compute-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  compute-children-combinator-Enriched-Directed-Tree :
    children-Enriched-Directed-Tree A B (T b) x ≃
    children-combinator-Enriched-Directed-Tree
  compute-children-combinator-Enriched-Directed-Tree =
    compute-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)
```

### If `e` is an edge from `node-inclusion i x` to `node-inclusion j y`, then `i ＝ j`

```agda
eq-index-edge-combinator-Enriched-Directed-Tree :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) (a : A)
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  {b : B a} (x : node-Enriched-Directed-Tree A B (T b))
  {c : B a} (y : node-Enriched-Directed-Tree A B (T c)) →
  edge-combinator-Enriched-Directed-Tree A B T
    ( node-inclusion-combinator-Directed-Tree b x)
    ( node-inclusion-combinator-Directed-Tree c y) →
  b ＝ c
eq-index-edge-combinator-Enriched-Directed-Tree A B a T =
  eq-index-edge-combinator-Directed-Tree
    ( directed-tree-Enriched-Directed-Tree A B ∘ T)
```
