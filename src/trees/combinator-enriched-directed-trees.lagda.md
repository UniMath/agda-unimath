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

open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.enriched-directed-trees
```

</details>

## Idea

Given an element `a : A` and a map `T : B(a) → Enriched-Directed-Tree A B`, we construct an enriched directed tree that combines the trees `T` into a single tree.

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
