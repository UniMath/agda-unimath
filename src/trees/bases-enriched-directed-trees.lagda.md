# Bases of enriched directed trees

```agda
module trees.bases-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.negation
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import trees.bases-directed-trees
open import trees.enriched-directed-trees
```

</details>

## Idea

The base of an enriched directed tree consists of its nodes equipped with an
edge to the root.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  base-Enriched-Directed-Tree : UU (l3 ⊔ l4)
  base-Enriched-Directed-Tree =
    children-Enriched-Directed-Tree A B T (root-Enriched-Directed-Tree A B T)

  module _
    (b : base-Enriched-Directed-Tree)
    where

    node-base-Enriched-Directed-Tree : node-Enriched-Directed-Tree A B T
    node-base-Enriched-Directed-Tree =
      node-base-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) b

    edge-base-Enriched-Directed-Tree :
      edge-Enriched-Directed-Tree A B T
        ( node-base-Enriched-Directed-Tree)
        ( root-Enriched-Directed-Tree A B T)
    edge-base-Enriched-Directed-Tree =
      edge-base-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T) b
```

## Properties

### The root is not a base element

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  is-not-root-node-base-Enriched-Directed-Tree :
    (b : base-Enriched-Directed-Tree A B T) →
    ¬ ( is-root-Enriched-Directed-Tree A B T
        ( node-base-Enriched-Directed-Tree A B T b))
  is-not-root-node-base-Enriched-Directed-Tree =
    is-not-root-node-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)

  no-walk-to-base-root-Enriched-Directed-Tree :
    (b : base-Enriched-Directed-Tree A B T) →
    ¬ ( walk-Enriched-Directed-Tree A B T
        ( root-Enriched-Directed-Tree A B T)
        ( node-base-Enriched-Directed-Tree A B T b))
  no-walk-to-base-root-Enriched-Directed-Tree =
    no-walk-to-base-root-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
```

### There are no edges between base elements

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  no-edge-base-Enriched-Directed-Tree :
    (a b : base-Enriched-Directed-Tree A B T) →
    ¬ ( edge-Enriched-Directed-Tree A B T
        ( node-base-Enriched-Directed-Tree A B T a)
        ( node-base-Enriched-Directed-Tree A B T b))
  no-edge-base-Enriched-Directed-Tree =
    no-edge-base-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T)
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  unique-walk-to-base-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    is-contr
      ( is-root-Enriched-Directed-Tree A B T x +
        Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-Enriched-Directed-Tree =
    unique-walk-to-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)

  is-root-or-walk-to-base-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    is-root-Enriched-Directed-Tree A B T x +
    Σ ( base-Enriched-Directed-Tree A B T)
      ( walk-Enriched-Directed-Tree A B T x ∘
        node-base-Enriched-Directed-Tree A B T)
  is-root-or-walk-to-base-Enriched-Directed-Tree =
    is-root-or-walk-to-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)

  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Tree :
    is-root-or-walk-to-base-Enriched-Directed-Tree
      ( root-Enriched-Directed-Tree A B T) ＝
    inl refl
  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Tree =
    is-root-is-root-or-walk-to-base-root-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)

  unique-walk-to-base-is-not-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    ¬ (is-root-Enriched-Directed-Tree A B T x) →
    is-contr
      ( Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-is-not-root-Enriched-Directed-Tree =
    unique-walk-to-base-is-not-root-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)

  unique-walk-to-base-parent-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T)
    (u :
      Σ ( node-Enriched-Directed-Tree A B T)
        ( edge-Enriched-Directed-Tree A B T x)) →
    is-contr
      ( Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-parent-Enriched-Directed-Tree =
    unique-walk-to-base-parent-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
```
