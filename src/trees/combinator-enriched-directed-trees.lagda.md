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

open import trees.bases-enriched-directed-trees
open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.enriched-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.fibers-enriched-directed-trees
open import trees.morphisms-enriched-directed-trees
```

</details>

## Idea

Given an element `a : A` and a map `T : B(a) → Enriched-Directed-Tree A B`, we
construct an enriched directed tree that combines the trees `T` into a single
tree.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) (a : A)
  (T : B a → Enriched-Directed-Tree l3 l4 A B)
  where

  directed-tree-combinator-Enriched-Directed-Tree :
    Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3 ⊔ l4)
  directed-tree-combinator-Enriched-Directed-Tree =
    combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

  node-combinator-Enriched-Directed-Tree : UU (l2 ⊔ l3)
  node-combinator-Enriched-Directed-Tree =
    node-combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

  root-combinator-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree
  root-combinator-Enriched-Directed-Tree = root-combinator-Directed-Tree

  edge-combinator-Enriched-Directed-Tree :
    (x y : node-combinator-Enriched-Directed-Tree) → UU (l2 ⊔ l3 ⊔ l4)
  edge-combinator-Enriched-Directed-Tree =
    edge-combinator-Directed-Tree (directed-tree-Enriched-Directed-Tree A B ∘ T)

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
    ( children-combinator-Directed-Tree
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

  map-children-combinator-Enriched-Directed-Tree :
    Σ ( node-Enriched-Directed-Tree A B (T b))
      ( λ y → edge-Enriched-Directed-Tree A B (T b) y x) →
    Σ ( node-combinator-Enriched-Directed-Tree A B a T)
      ( λ y →
        edge-combinator-Enriched-Directed-Tree A B a T y
          ( node-inclusion-combinator-Directed-Tree b x))
  map-children-combinator-Enriched-Directed-Tree =
    map-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  is-equiv-map-children-combinator-Enriched-Directed-Tree :
    is-equiv map-children-combinator-Enriched-Directed-Tree
  is-equiv-map-children-combinator-Enriched-Directed-Tree =
    is-equiv-map-children-combinator-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B ∘ T)
      ( b)
      ( x)

  children-combinator-Enriched-Directed-Tree :
    Σ ( node-Enriched-Directed-Tree A B (T b))
      ( λ y → edge-Enriched-Directed-Tree A B (T b) y x) ≃
    Σ ( node-combinator-Enriched-Directed-Tree A B a T)
      ( λ y →
        edge-combinator-Enriched-Directed-Tree A B a T y
          ( node-inclusion-combinator-Directed-Tree b x))
  children-combinator-Enriched-Directed-Tree =
    children-combinator-Directed-Tree
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
  edge-combinator-Enriched-Directed-Tree A B a T
    ( node-inclusion-combinator-Directed-Tree b x)
    ( node-inclusion-combinator-Directed-Tree c y) →
  b ＝ c
eq-index-edge-combinator-Enriched-Directed-Tree A B a T =
  eq-index-edge-combinator-Directed-Tree
    ( directed-tree-Enriched-Directed-Tree A B ∘ T)
```

### Any tree is the combinator tree of the fibers at the nodes equipped with edges to the root

````agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  node-combinator-fiber-base-Enriched-Directed-Tree :
    node-combinator-Enriched-Directed-Tree A B
      ( shape-root-Enriched-Directed-Tree A B T)
      ( fiber-base-Enriched-Directed-Tree A B T ∘ {!!})
      -- ( fiber-base-Enriched-Directed-Tree A B T ?)
      →
    node-Enriched-Directed-Tree A B T
  node-combinator-fiber-base-Enriched-Directed-Tree = {!!}

{-
    node-combinator-fiber-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
-}

--   is-equiv-node-combinator-fiber-base-Enriched-Directed-Tree :
--     is-equiv node-combinator-fiber-base-Enriched-Directed-Tree
--   is-equiv-node-combinator-fiber-base-Enriched-Directed-Tree =
--     is-equiv-node-combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)

--   equiv-node-combinator-fiber-base-Enriched-Directed-Tree :
--     node-combinator-Enriched-Directed-Tree
--       ( fiber-base-Enriched-Directed-Tree T) ≃
--     node-Enriched-Directed-Tree T
--   equiv-node-combinator-fiber-base-Enriched-Directed-Tree =
--     equiv-node-combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)

--   edge-combinator-fiber-base-Enriched-Directed-Tree :
--     (x y :
--       node-combinator-Enriched-Directed-Tree
--         ( fiber-base-Enriched-Directed-Tree A B T)) →
--     edge-combinator-Enriched-Directed-Tree
--       ( fiber-base-Enriched-Directed-Tree A B T) x y →
--     edge-Enriched-Directed-Tree A B T
--       ( node-combinator-fiber-base-Enriched-Directed-Tree x)
--       ( node-combinator-fiber-base-Enriched-Directed-Tree y)
--   edge-combinator-fiber-base-Enriched-Directed-Tree =
--     edge-combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)

--   hom-combinator-fiber-base-Enriched-Directed-Tree :
--     hom-Enriched-Directed-Tree A B
--       ( combinator-Enriched-Directed-Tree A B
--         ( fiber-base-Enriched-Directed-Tree A B T))
--       ( T)
--   hom-combinator-fiber-base-Enriched-Directed-Tree =
--     hom-combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)

--   is-equiv-directed-tree-combinator-fiber-base-Enriched-Directed-Tree :
--     is-equiv-hom-Enriched-Directed-Tree A B
--       ( combinator-Enriched-Directed-Tree A B
--         ( fiber-base-Enriched-Directed-Tree A B T))
--       ( T)
--       ( hom-combinator-fiber-base-Enriched-Directed-Tree)
--   is-equiv-directed-tree-combinator-fiber-base-Enriched-Directed-Tree =
--     is-equiv-combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)

--   equiv-directed-tree-combinator-fiber-base-Enriched-Directed-Tree :
--     equiv-Enriched-Directed-Tree A B
--       ( combinator-Enriched-Directed-Tree A B
--         ( fiber-base-Enriched-Directed-Tree A B T))
--       ( T)
--   equiv-directed-tree-combinator-fiber-base-Enriched-Directed-Tree =
--     combinator-fiber-base-Directed-Tree
--       ( directed-tree-Enriched-Directed-Tree A B T)
-- ```
````
