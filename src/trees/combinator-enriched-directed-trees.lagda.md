# Combinators of enriched directed trees

```agda
module trees.combinator-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.maybe
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.fibers-enriched-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

The
{{#concept "combinator operation" Disambiguation="on enriched directed trees" Agda=combinator-Enriched-Directed-Tree}}
on [enriched directed trees](trees.enriched-directed-trees.md) combines, for any
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

  unique-direct-successor-combinator-Enriched-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-combinator-Enriched-Directed-Tree)
      ( root-combinator-Enriched-Directed-Tree)
  unique-direct-successor-combinator-Enriched-Directed-Tree =
    unique-direct-successor-combinator-Directed-Tree
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

  is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Tree :
    ( map-root-enrichment-combinator-Enriched-Directed-Tree ∘
      map-inv-root-enrichment-combinator-Enriched-Directed-Tree) ~ id
  is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Tree
    ( ._ , edge-to-root-combinator-Directed-Tree b) = refl

  is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Tree :
    ( map-inv-root-enrichment-combinator-Enriched-Directed-Tree ∘
      map-root-enrichment-combinator-Enriched-Directed-Tree) ~ id
  is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Tree b =
    refl

  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Tree :
    is-equiv map-root-enrichment-combinator-Enriched-Directed-Tree
  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Tree =
    is-equiv-is-invertible
      map-inv-root-enrichment-combinator-Enriched-Directed-Tree
      is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Tree
      is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Tree

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
    ( compute-direct-predecessor-combinator-Directed-Tree
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

### The type of direct-predecessor of `x : T b` is equivalent to the type of direct-predecessor of the inclusion of `x` in `combinator T`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A} (b : B a)
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  (x : node-Enriched-Directed-Tree A B (T b))
  where

  direct-predecessor-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3 ⊔ l4)
  direct-predecessor-combinator-Enriched-Directed-Tree =
    direct-predecessor-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  map-compute-direct-predecessor-combinator-Enriched-Directed-Tree :
    direct-predecessor-Enriched-Directed-Tree A B (T b) x →
    direct-predecessor-combinator-Enriched-Directed-Tree
  map-compute-direct-predecessor-combinator-Enriched-Directed-Tree =
    map-compute-direct-predecessor-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  is-equiv-map-compute-direct-predecessor-combinator-Enriched-Directed-Tree :
    is-equiv map-compute-direct-predecessor-combinator-Enriched-Directed-Tree
  is-equiv-map-compute-direct-predecessor-combinator-Enriched-Directed-Tree =
    is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  compute-direct-predecessor-combinator-Enriched-Directed-Tree :
    direct-predecessor-Enriched-Directed-Tree A B (T b) x ≃
    direct-predecessor-combinator-Enriched-Directed-Tree
  compute-direct-predecessor-combinator-Enriched-Directed-Tree =
    compute-direct-predecessor-combinator-Directed-Tree
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

### The base of the combinator tree of a family `T` of enriched directed tree indexed by `B a` is equivalent to `B a`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A}
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  node-base-index-combinator-Enriched-Directed-Tree :
    B a → node-combinator-Enriched-Directed-Tree A B T
  node-base-index-combinator-Enriched-Directed-Tree =
    node-base-index-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  edge-base-index-combinator-Enriched-Directed-Tree :
    (b : B a) →
    edge-combinator-Enriched-Directed-Tree A B T
      ( node-base-index-combinator-Enriched-Directed-Tree b)
      ( root-combinator-Enriched-Directed-Tree A B T)
  edge-base-index-combinator-Enriched-Directed-Tree =
    edge-base-index-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  base-index-combinator-Enriched-Directed-Tree :
    B a → base-combinator-Enriched-Directed-Tree A B T
  base-index-combinator-Enriched-Directed-Tree =
    base-index-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  index-base-combinator-Enriched-Directed-Tree :
    base-combinator-Enriched-Directed-Tree A B T → B a
  index-base-combinator-Enriched-Directed-Tree =
    index-base-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-section-index-base-combinator-Enriched-Directed-Tree :
    ( base-index-combinator-Enriched-Directed-Tree ∘
      index-base-combinator-Enriched-Directed-Tree) ~ id
  is-section-index-base-combinator-Enriched-Directed-Tree =
    is-section-index-base-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-retraction-index-base-combinator-Enriched-Directed-Tree :
    ( index-base-combinator-Enriched-Directed-Tree ∘
      base-index-combinator-Enriched-Directed-Tree) ~ id
  is-retraction-index-base-combinator-Enriched-Directed-Tree =
    is-retraction-index-base-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-equiv-base-index-combinator-Enriched-Directed-Tree :
    is-equiv base-index-combinator-Enriched-Directed-Tree
  is-equiv-base-index-combinator-Enriched-Directed-Tree =
    is-equiv-base-index-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  equiv-base-index-combinator-Enriched-Directed-Tree :
    B a ≃ base-combinator-Enriched-Directed-Tree A B T
  equiv-base-index-combinator-Enriched-Directed-Tree =
    equiv-base-index-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
```

### The type of nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T b`, plus a root

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A}
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  map-compute-node-combinator-Enriched-Directed-Tree :
    Maybe (Σ (B a) (node-Enriched-Directed-Tree A B ∘ T)) →
    node-combinator-Enriched-Directed-Tree A B T
  map-compute-node-combinator-Enriched-Directed-Tree =
    map-compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  map-inv-compute-node-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree A B T →
    Maybe (Σ (B a) (node-Enriched-Directed-Tree A B ∘ T))
  map-inv-compute-node-combinator-Enriched-Directed-Tree =
    map-inv-compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-section-map-inv-compute-node-combinator-Enriched-Directed-Tree :
    ( map-compute-node-combinator-Enriched-Directed-Tree ∘
      map-inv-compute-node-combinator-Enriched-Directed-Tree) ~ id
  is-section-map-inv-compute-node-combinator-Enriched-Directed-Tree =
    is-section-map-inv-compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-retraction-map-inv-compute-node-combinator-Enriched-Directed-Tree :
    ( map-inv-compute-node-combinator-Enriched-Directed-Tree ∘
      map-compute-node-combinator-Enriched-Directed-Tree) ~ id
  is-retraction-map-inv-compute-node-combinator-Enriched-Directed-Tree =
    is-retraction-map-inv-compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-equiv-map-compute-node-combinator-Enriched-Directed-Tree :
    is-equiv map-compute-node-combinator-Enriched-Directed-Tree
  is-equiv-map-compute-node-combinator-Enriched-Directed-Tree =
    is-equiv-map-compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  compute-node-combinator-Enriched-Directed-Tree :
    Maybe (Σ (B a) (node-Enriched-Directed-Tree A B ∘ T)) ≃
    node-combinator-Enriched-Directed-Tree A B T
  compute-node-combinator-Enriched-Directed-Tree =
    compute-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
```

### The type of proper nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T b`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A}
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  map-compute-proper-node-combinator-Enriched-Directed-Tree :
    Σ (B a) (node-Enriched-Directed-Tree A B ∘ T) →
    proper-node-combinator-Enriched-Directed-Tree A B T
  map-compute-proper-node-combinator-Enriched-Directed-Tree =
    map-compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  map-inv-compute-proper-node-combinator-Enriched-Directed-Tree :
    proper-node-combinator-Enriched-Directed-Tree A B T →
    Σ (B a) (node-Enriched-Directed-Tree A B ∘ T)
  map-inv-compute-proper-node-combinator-Enriched-Directed-Tree =
    map-inv-compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-section-map-inv-compute-proper-node-combinator-Enriched-Directed-Tree :
    ( map-compute-proper-node-combinator-Enriched-Directed-Tree ∘
      map-inv-compute-proper-node-combinator-Enriched-Directed-Tree) ~ id
  is-section-map-inv-compute-proper-node-combinator-Enriched-Directed-Tree =
    is-section-map-inv-compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-retraction-map-inv-compute-proper-node-combinator-Enriched-Directed-Tree :
    ( map-inv-compute-proper-node-combinator-Enriched-Directed-Tree ∘
      map-compute-proper-node-combinator-Enriched-Directed-Tree) ~ id
  is-retraction-map-inv-compute-proper-node-combinator-Enriched-Directed-Tree =
    is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  is-equiv-map-compute-proper-node-combinator-Enriched-Directed-Tree :
    is-equiv map-compute-proper-node-combinator-Enriched-Directed-Tree
  is-equiv-map-compute-proper-node-combinator-Enriched-Directed-Tree =
    is-equiv-map-compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  compute-proper-node-combinator-Enriched-Directed-Tree :
    Σ (B a) (node-Enriched-Directed-Tree A B ∘ T) ≃
    proper-node-combinator-Enriched-Directed-Tree A B T
  compute-proper-node-combinator-Enriched-Directed-Tree =
    compute-proper-node-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
```

### The fibers at a base element `b : B a` of the comibinator of a family `T` of trees is equivalent to `T b`

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {a : A}
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  node-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    node-Enriched-Directed-Tree A B (T b) →
    node-fiber-Enriched-Directed-Tree A B
      ( combinator-Enriched-Directed-Tree A B T)
      ( node-base-index-combinator-Enriched-Directed-Tree A B T b)
  node-compute-fiber-combinator-Enriched-Directed-Tree =
    node-fiber-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  edge-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) (x y : node-Enriched-Directed-Tree A B (T b)) →
    edge-Enriched-Directed-Tree A B (T b) x y →
    edge-fiber-Enriched-Directed-Tree A B
      ( combinator-Enriched-Directed-Tree A B T)
      ( node-base-index-combinator-Enriched-Directed-Tree A B T b)
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b x)
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b y)
  edge-compute-fiber-combinator-Enriched-Directed-Tree =
    edge-fiber-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B (T b))
      ( directed-tree-fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b))
  directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree =
    hom-fiber-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  direct-predecessor-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) (x : node-Enriched-Directed-Tree A B (T b)) →
    direct-predecessor-Enriched-Directed-Tree A B (T b) x →
    direct-predecessor-fiber-Enriched-Directed-Tree A B
      ( combinator-Enriched-Directed-Tree A B T)
      ( node-base-index-combinator-Enriched-Directed-Tree A B T b)
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b x)
  direct-predecessor-compute-fiber-combinator-Enriched-Directed-Tree b =
    direct-predecessor-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B (T b))
      ( directed-tree-fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b))
      ( directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree b)

  is-equiv-directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    is-equiv-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B (T b))
      ( directed-tree-fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b))
      ( directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree b)
  is-equiv-directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Tree =
    is-equiv-hom-fiber-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B (T b))
      ( directed-tree-fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b))
  equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Tree =
    fiber-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)

  shape-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    ( shape-Enriched-Directed-Tree A B (T b)) ~
    ( ( shape-fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b)) ∘
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b))
  shape-compute-fiber-combinator-Enriched-Directed-Tree b x = refl

  enrichment-compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) (x : node-Enriched-Directed-Tree A B (T b)) →
    ( ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Tree
        ( b)
        ( x)) ∘
      ( map-enrichment-Enriched-Directed-Tree A B (T b) x)) ~
    ( map-enrichment-fiber-base-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( b)
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b x))
  enrichment-compute-fiber-combinator-Enriched-Directed-Tree b x y =
    eq-map-enrichment-fiber-Enriched-Directed-Tree A B
      ( combinator-Enriched-Directed-Tree A B T)
      ( node-base-index-combinator-Enriched-Directed-Tree A B T b)
      ( node-compute-fiber-combinator-Enriched-Directed-Tree b x)
      ( y)
      ( pr2
        ( pr1
          ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Tree
            ( b)
            ( x)
            ( map-enrichment-Enriched-Directed-Tree A B (T b) x y))))
      ( pr2
        ( pr2
          ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Tree
            ( b)
            ( x)
            ( map-enrichment-Enriched-Directed-Tree A B (T b) x y))))

  compute-fiber-combinator-Enriched-Directed-Tree :
    (b : B a) →
    equiv-Enriched-Directed-Tree A B
      ( T b)
      ( fiber-Enriched-Directed-Tree A B
        ( combinator-Enriched-Directed-Tree A B T)
        ( node-base-index-combinator-Enriched-Directed-Tree A B T b))
  pr1 (compute-fiber-combinator-Enriched-Directed-Tree b) =
    equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Tree b
  pr1 (pr2 (compute-fiber-combinator-Enriched-Directed-Tree b)) =
    shape-compute-fiber-combinator-Enriched-Directed-Tree b
  pr2 (pr2 (compute-fiber-combinator-Enriched-Directed-Tree b)) =
    enrichment-compute-fiber-combinator-Enriched-Directed-Tree b
```
